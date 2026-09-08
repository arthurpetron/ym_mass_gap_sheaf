/-
# Uniform density calibration controls the full posterior relative cost

The connected and disconnected receiver transports share the same physical
source and target density coefficients.  A common absolute calibration bound
on the full source four-cell, together with one on the full target four-cell,
therefore controls both split posterior sectors.  Their already-proved
physical column capacities make each sector sum against target mass rather
than carrier cardinality.  Exact Boolean reassembly then gives

```text
fullCarrierPosteriorDensityL1
  <= (sourceRelative + targetRelative) * fullCarrierTargetMass,
```

and hence the same ceiling for the total normalized posterior relative cost.

No calibration estimate is inhabited here.  In particular, this proves no
quadratic coupling bound, lower spacing law, continuum limit, OS/GNS
reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: finite rational inequalities and the explicit split
kernels only; no choice, `Classical`, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost
import YMGap.Continuum.FiniteDependentKernelCoefficientPosteriorRelativeBound

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierUniformCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance uniformCalibrationPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

local instance uniformCalibrationReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  splitTransportPairDecidableEq S root

/-- Uniform calibration on the two full four-cell carriers controls the
connected posterior sector without a target-cardinality factor. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1_le_uniformCalibration
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          sourceRelative)
    (htargetCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          targetRelative) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    connected.posteriorColumnCoefficientL1 ≤
      (sourceRelative + targetRelative) *
        listQSum connected.targetWeight connected.targets := by
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  apply connected.posteriorColumnCoefficientL1_le_uniformCoefficientBounds
    sourceRelative targetRelative hsourceRelative
  · intro source _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root source.1
  · intro source choice _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservablePairedConnectedStrandThinnedWeight_nonnegative
        S.coarse root target htarget source choice
  · intro source _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients]
      using hsourceCoefficient source.1
        (List.mem_filter.mp source.2).1
  · intro receiver _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root receiver
  · intro receiver hreceiver
    have hreceiver' : receiver ∈
        slabObservablePairedSupportConnectedFourCellTargetPairs
          S.coarse root target := by
      simpa only [connected,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
        FiniteDependentCoefficientTransport.replaceCoefficients,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
        using hreceiver
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients]
      using htargetCoefficient receiver
        (List.mem_filter.mp hreceiver').1
  · intro receiver _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservablePairedConnectedStrandThinnedWeightedColumn_le
        S.coarse root target htarget receiver

/-- The same two full-carrier calibration bounds control the normalized
disconnected posterior sector. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1_le_uniformCalibration
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          sourceRelative)
    (htargetCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          targetRelative) :
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    disconnected.posteriorColumnCoefficientL1 ≤
      (sourceRelative + targetRelative) *
        listQSum disconnected.targetWeight disconnected.targets := by
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  apply disconnected.posteriorColumnCoefficientL1_le_uniformCoefficientBounds
    sourceRelative targetRelative hsourceRelative
  · intro source _
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root source.1
  · intro source choice _
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using slabObservablePairedSupportRecouplingWeight_nonnegative
        S.coarse root target htarget source choice
  · intro source _
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients]
      using hsourceCoefficient source.1 source.pair_mem_fourCell
  · intro receiver _
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root receiver
  · intro receiver hreceiver
    have hreceiver' : receiver ∈
        slabObservablePairedSupportDisconnectedFourCellTargetPairs
          S.coarse root target := by
      simpa only [disconnected,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
        FiniteDependentCoefficientTransport.replaceCoefficients,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
        using hreceiver
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients]
      using htargetCoefficient receiver
        (List.mem_filter.mp hreceiver').1
  · intro receiver _
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using
      slabObservablePairedSupportSeparatedWeightedColumn_le_disconnectedTarget
        S.coarse root target htarget receiver

/-- Connected and disconnected column capacities reassemble the two uniform
calibration bounds on the literal full target carrier. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_uniformCalibration
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (hsourceCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          sourceRelative)
    (htargetCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          targetRelative) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
        S hfineCutoff hcoarseCoupling root target htarget ≤
      (sourceRelative + targetRelative) *
        actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
          S root target := by
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1_le_uniformCalibration
      S hfineCutoff hcoarseCoupling root target htarget
      sourceRelative targetRelative hsourceRelative
      hsourceCoefficient htargetCoefficient
  have hdisconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1_le_uniformCalibration
      S hfineCutoff hcoarseCoupling root target htarget
      sourceRelative targetRelative hsourceRelative
      hsourceCoefficient htargetCoefficient
  have hsplit :
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
          S hfineCutoff hcoarseCoupling root target htarget ≤
        connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 :=
    Q'.le_of_eqv
      (actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_eqv_split
        S hfineCutoff hcoarseCoupling root target htarget)
  have hbranches :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        (sourceRelative + targetRelative) *
            listQSum connected.targetWeight connected.targets +
          (sourceRelative + targetRelative) *
            listQSum disconnected.targetWeight disconnected.targets := by
    exact Q'.add_le_add
      (by simpa only [connected] using hconnected)
      (by simpa only [disconnected] using hdisconnected)
  have hreassemble :
      (sourceRelative + targetRelative) *
            listQSum connected.targetWeight connected.targets +
          (sourceRelative + targetRelative) *
            listQSum disconnected.targetWeight disconnected.targets ≈
        (sourceRelative + targetRelative) *
          actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
            S root target := by
    refine Q'.eqv_trans _
      ((sourceRelative + targetRelative) *
        (listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_add_eqv (sourceRelative + targetRelative)
          (listQSum connected.targetWeight connected.targets)
          (listQSum disconnected.targetWeight disconnected.targets))
    · apply Q'.mul_eqv_congr_left (sourceRelative + targetRelative)
      simpa only [connected, disconnected,
        actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass]
        using splitDensityTransports_targetWeight_eqv_fourCellTargetWeight
          S hfineCutoff hcoarseCoupling root target htarget
  exact Q'.le_trans' _ _ _ hsplit
    (Q'.le_trans' _ _ _ hbranches (Q'.le_of_eqv hreassemble))

/-- Uniform source and target density calibration leaves only their sum as
the normalized full-carrier posterior relative cost. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_le_uniformCalibration
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (sourceRelative targetRelative : Q')
    (hsourceRelative : (0 : Q') ≤ sourceRelative)
    (htargetRelative : (0 : Q') ≤ targetRelative)
    (hsourceCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellSourcePairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          sourceRelative)
    (htargetCoefficient : ∀ receiver,
      receiver ∈ slabObservableFourCellTargetPairs S.coarse root target →
        Q'.abs
            (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
              S hfineCutoff hcoarseCoupling root target receiver) ≤
          targetRelative) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
        S hfineCutoff hcoarseCoupling root target htarget ≤
      sourceRelative + targetRelative := by
  apply
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_le_of_densityL1_le
      S hfineCutoff hcoarseCoupling root target htarget
      (sourceRelative + targetRelative)
      (Q'.zero_le_add sourceRelative targetRelative
        hsourceRelative htargetRelative)
  exact
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_uniformCalibration
      S hfineCutoff hcoarseCoupling root target htarget
      sourceRelative targetRelative hsourceRelative
      hsourceCoefficient htargetCoefficient

#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1_le_uniformCalibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1_le_uniformCalibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_uniformCalibration
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_le_uniformCalibration

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierUniformCalibration
