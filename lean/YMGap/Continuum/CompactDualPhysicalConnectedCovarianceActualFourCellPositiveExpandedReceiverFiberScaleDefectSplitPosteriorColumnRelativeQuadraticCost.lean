/-
# Relative receiver-column inputs imply the global posterior quadratic cost

The normalized posterior route needs one global three-term estimate.  A
uniform estimate per receiver column would lose the size of the growing
finite carrier.  This module replaces that global input by one aggregate
connected-row estimate and one literal posterior estimate over the original
full opposite four-cell target carrier, relative to their actual physical
masses.  Combined-sector, separate-sector, and pointwise weight-relative
estimates are retained as sufficient interfaces.

The connected source carrier and the full opposite target carrier both sit
inside the positive-first-replica product carrier.  Their weight is therefore
bounded without cardinality loss by the coarse physical partition square.
The connected and disconnected posterior columns reassemble exactly on that
full carrier, so their common relative column ceiling is paid only once.
Finally

```text
partitionDensity * Z_coarse^2 = Z_fine^2
```

converts the local relative bounds into precisely the global quadratic input
consumed by the matched-AF posterior bridge.

No aggregate or pointwise relative estimate, raw-mismatch estimate, or lower
physical-spacing law is inhabited here.  The result is a volume-safe finite
reduction, not a continuum construction, OS/GNS reconstruction, Hamiltonian
gap, or Clay conclusion.

Constructive contract: exact rational finite sums, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientPosteriorRelativeBound
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
import YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance relativeQuadraticPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

local instance relativeQuadraticReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  splitTransportPairDecidableEq S root

private theorem targetPair_mem_positiveTimesAll
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellTargetPairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have htarget :=
    (mem_cartesian_iff
      (slabObservableRootTargetComplementEntries D root target)
      (slabObservableRootComplementTargetEntries D root target)
      pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp htarget.1).1,
    (List.mem_filter.mp htarget.2).1⟩

/-- The entire opposite four-cell target carrier has mass at most the
two-replica physical partition. -/
theorem slabObservableFourCellTargetPairs_weight_le_partitionSquare
    (D : SlabPhysicalData) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs D root target) ≤
      D.physicalPartition * D.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs D root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePositiveTimesAllPairs D root) := by
    apply listQSum_le_of_injective
      (slabObservableFourCellTargetPairs D root target)
      (slabObservablePositiveTimesAllPairs D root)
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      (slabObservableFourCellTargetPairs_nodup D root target)
    · intro pair hpair
      exact targetPair_mem_positiveTimesAll D root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_nonnegative D root pair
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition D root
  have hpositive :
      slabObservablePositiveSourceWeight D root ≤ D.physicalPartition :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (slabObservablePositiveSourceWeight D root) 1 (by decide))
      hpositiveAdd
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (slabObservablePositiveSourceWeight D root)
    D.physicalPartition D.physicalPartition hpositive
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservablePositiveTimesAllPairs_weight_eqv D root))
      hscaled)

/-- The connected source list used by the density transport has total source
weight at most the coarse physical partition square. -/
theorem connectedDensityTransport_sourceWeight_le_coarseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let data :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    listQSum data.sourceWeight data.sources ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  dsimp only
  let data :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have halign :
      listQSum data.sourceWeight data.sources ≈
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.coarse root target) := by
    unfold data
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      FiniteDependentCoefficientTransport.replaceCoefficients
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      slabObservablePairedConnectedStrandSources
    exact Q'.eqv_of_eq
      (listQSum_attach
        (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target))
  have hconnected :=
    slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
      S.coarse root target
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition S.coarse root
  have hpositive :
      slabObservablePositiveSourceWeight S.coarse root ≤
        S.coarse.physicalPartition :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (slabObservablePositiveSourceWeight S.coarse root) 1 (by decide))
      hpositiveAdd
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (slabObservablePositiveSourceWeight S.coarse root)
    S.coarse.physicalPartition S.coarse.physicalPartition hpositive
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halign)
    (Q'.le_trans' _ _ _ hconnected hscaled)

/-- The connected and disconnected density transports use complementary
target sectors, so their target weights together cost at most one coarse
partition square. -/
theorem splitDensityTransports_targetWeight_le_coarseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    listQSum connected.targetWeight connected.targets +
        listQSum disconnected.targetWeight disconnected.targets ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  dsimp only
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hpartition :=
    slabObservableFourCellTargetPairs_pairedSupport_partition
      S.coarse root target
  have halign :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≈
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target) := by
    simpa only [connected, disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
      using Q'.eqv_symm hpartition
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halign)
    (slabObservableFourCellTargetPairs_weight_le_partitionSquare
      S.coarse root target)

theorem positiveExpandedReceiverFiberPartitionDensity_pos
    (S : SlabScalePair) :
    (0 : Q') < positiveExpandedReceiverFiberPartitionDensity S := by
  unfold positiveExpandedReceiverFiberPartitionDensity
  exact Q'.divPos_pos _ _ (coarsePhysicalPartitionSquare_pos S)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

/-- The literal connected-row density `l1` budget majorizes the signed row
debt used by the posterior compiler. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt_abs_le_densityDefectL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
  apply receiverTransportRowCoefficientDefect_abs_le_densityDefectL1
  intro source
  exact Q'.eqv_refl _

/-! ## 2. Coverage-insensitive aggregate coefficient calibration -/

/-- Full physical-weighted absolute source density-coefficient mass.  This is
the dimensionless version of the direct source calibration budget. -/
def actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      slabObservableTwoReplicaPairWeight S.coarse receiver *
        Q'.abs
          (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
            S hfineCutoff hcoarseCoupling root target receiver))
    (slabObservableFourCellSourcePairs S.coarse root target)

/-- Full physical-weighted absolute target density-coefficient mass. -/
def actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      slabObservableTwoReplicaPairWeight S.coarse receiver *
        Q'.abs
          (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
            S hfineCutoff hcoarseCoupling root target receiver))
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- The connected and disconnected transports partition the full source
coefficient `l1` mass exactly. -/
theorem splitDensityTransports_sourceCoefficientL1_eqv_full
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    connected.sourceCoefficientL1 + disconnected.sourceCoefficientL1 ≈
      actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target := by
  dsimp only
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let term := fun receiver : Receiver S root =>
    slabObservableTwoReplicaPairWeight S.coarse receiver *
      Q'.abs
        (actualPositiveExpandedReceiverFiberSourceDensityCoefficient
          S hfineCutoff hcoarseCoupling root target receiver)
  let sector := fun receiver : Receiver S root =>
    slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver
  have hconnected :
      connected.sourceCoefficientL1 ≈
        listQSum term
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.coarse root target) := by
    unfold sourceCoefficientL1
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
      slabObservablePairedConnectedStrandSources, term] using
        Q'.eqv_of_eq
          (listQSum_attach term
            (slabObservablePairedSupportConnectedFourCellSourcePairs
              S.coarse root target))
  have hdisconnected :
      disconnected.sourceCoefficientL1 ≈
        listQSum term
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            S.coarse root target) := by
    unfold sourceCoefficientL1
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport,
      slabObservablePairedSupportSeparatedSources, term] using
        Q'.eqv_of_eq
          (listQSum_attach term
            (slabObservablePairedSupportSeparatedFourCellSourcePairs
              S.coarse root target))
  have hpartition := listQSum_filter_partition term sector
    (slabObservableFourCellSourcePairs S.coarse root target)
  refine Q'.eqv_trans _
    (listQSum term
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) +
      listQSum term
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          S.coarse root target)) _
    (Q'.add_eqv_congr' hconnected hdisconnected) ?_
  simpa only [sector,
    slabObservablePairedSupportConnectedFourCellSourcePairs,
    slabObservablePairedSupportSeparatedFourCellSourcePairs,
    actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1,
    term] using Q'.eqv_symm hpartition

/-- The target support predicate partitions the full target coefficient `l1`
mass in the same order as the two posterior sectors. -/
theorem splitDensityTransports_targetCoefficientL1_eqv_full
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    connected.targetCoefficientL1 + disconnected.targetCoefficientL1 ≈
      actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
        S hfineCutoff hcoarseCoupling root target := by
  dsimp only
  let term := fun receiver : Receiver S root =>
    slabObservableTwoReplicaPairWeight S.coarse receiver *
      Q'.abs
        (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
          S hfineCutoff hcoarseCoupling root target receiver)
  let sector := fun receiver : Receiver S root =>
    slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver
  have hpartition := listQSum_filter_partition term sector
    (slabObservableFourCellTargetPairs S.coarse root target)
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
    FiniteDependentCoefficientTransport.replaceCoefficients,
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport,
    sourceCoefficientL1, targetCoefficientL1, sector,
    slabObservablePairedSupportConnectedFourCellTargetPairs,
    slabObservablePairedSupportDisconnectedFourCellTargetPairs,
    actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1,
    term] using Q'.eqv_symm hpartition

/-- The actual connected row plus both posterior sectors are controlled by
one full-source plus full-target coefficient `l1` budget.  The estimate is
insensitive to receiver points outside the supported-path image. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorDensityBudget_le_fullCoefficientL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S hfineCutoff hcoarseCoupling root target htarget
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
            S hfineCutoff hcoarseCoupling root target +
          actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
            S hfineCutoff hcoarseCoupling root target := by
  dsimp only
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hconnected :
      Q'.abs connected.rowCoefficientDefect +
          connected.posteriorColumnCoefficientL1 ≤
        connected.sourceCoefficientL1 + connected.targetCoefficientL1 := by
    apply connected.rowAbs_add_posteriorColumnL1_le_source_add_targetCoefficientL1
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
    · intro receiver _
      simpa only [connected,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
        FiniteDependentCoefficientTransport.replaceCoefficients,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
        using slabObservableTwoReplicaPairWeight_nonnegative
          S.coarse root receiver
    · intro source _
      simpa only [connected,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
        FiniteDependentCoefficientTransport.replaceCoefficients,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
        using slabObservablePairedConnectedStrandThinnedRowMass_le_one
          S.coarse root target htarget source
  have hdisconnectedFull :
      Q'.abs disconnected.rowCoefficientDefect +
          disconnected.posteriorColumnCoefficientL1 ≤
        disconnected.sourceCoefficientL1 +
          disconnected.targetCoefficientL1 := by
    apply disconnected.rowAbs_add_posteriorColumnL1_le_source_add_targetCoefficientL1
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
    · intro receiver _
      simpa only [disconnected,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
        FiniteDependentCoefficientTransport.replaceCoefficients,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
        using slabObservableTwoReplicaPairWeight_nonnegative
          S.coarse root receiver
    · intro source _
      change (1 : Q') ≤ 1
      exact Q'.le_refl' 1
  have hdisconnected :
      disconnected.posteriorColumnCoefficientL1 ≤
        disconnected.sourceCoefficientL1 +
          disconnected.targetCoefficientL1 := by
    refine Q'.le_trans' _
      (Q'.abs disconnected.rowCoefficientDefect +
        disconnected.posteriorColumnCoefficientL1) _ ?_ hdisconnectedFull
    refine Q'.le_trans' _
      (disconnected.posteriorColumnCoefficientL1 +
        Q'.abs disconnected.rowCoefficientDefect) _
      (Q'.add_le_self_of_nonneg
        disconnected.posteriorColumnCoefficientL1
        (Q'.abs disconnected.rowCoefficientDefect)
        (Q'.abs_nonneg disconnected.rowCoefficientDefect)) ?_
    exact Q'.le_of_eqv
      (Q'.add_comm_eqv
        disconnected.posteriorColumnCoefficientL1
        (Q'.abs disconnected.rowCoefficientDefect))
  have hsum := Q'.add_le_add hconnected hdisconnected
  have hsource := splitDensityTransports_sourceCoefficientL1_eqv_full
    S hfineCutoff hcoarseCoupling root target htarget
  have htarget := splitDensityTransports_targetCoefficientL1_eqv_full
    S hfineCutoff hcoarseCoupling root target htarget
  refine Q'.le_trans' _
    ((connected.sourceCoefficientL1 + connected.targetCoefficientL1) +
      (disconnected.sourceCoefficientL1 + disconnected.targetCoefficientL1)) _
    hsum ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _
    ((connected.sourceCoefficientL1 + disconnected.sourceCoefficientL1) +
      (connected.targetCoefficientL1 + disconnected.targetCoefficientL1)) _
    (Q'.add_swap_inner
      connected.sourceCoefficientL1 connected.targetCoefficientL1
      disconnected.sourceCoefficientL1 disconnected.targetCoefficientL1) ?_)
  exact Q'.add_eqv_congr' hsource htarget

/-- The dimensionless three-term posterior budget is bounded directly by the
one full-carrier coefficient `l1` sum. -/
theorem splitPosteriorColumnBudget_le_fullCoefficientL1Raw
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget +
        actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hbudget :=
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorDensityBudget_le_fullCoefficientL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  refine Q'.le_trans' _
    ((Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1) _ ?_ ?_
  · exact Q'.le_of_eqv (by
      unfold actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
      simp only [S, root, target, connected, disconnected,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1]
      apply Q'.eqv_of_eq
      congr <;> apply Subsingleton.elim)
  · exact Q'.le_trans' _ _ _
      (by simpa only [S, root, target, htarget, connected, disconnected]
        using hbudget)
      (Q'.le_refl' _)

/-- One aggregate full-carrier coefficient estimate is sufficient for the
dimensionless three-term posterior budget.  This is now the weakest preferred
finite analytic interface on this route. -/
theorem splitPosteriorColumnBudget_le_fullCoefficientL1
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (ceiling : Q')
    (hcoefficientL1 :
      let S := schedule.scalePair scale
      let root := (schedule.faceMap scale).coarseRoot
      let target := (schedule.faceMap scale).coarseTarget
      actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
            S rfl (schedule.effectiveCoupling_pos scale) root target +
          actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
            S rfl (schedule.effectiveCoupling_pos scale) root target ≤
        ceiling *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      ceiling *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) :=
  Q'.le_trans' _ _ _
    (splitPosteriorColumnBudget_le_fullCoefficientL1Raw schedule scale)
    hcoefficientL1

private theorem relativeQuadraticBudget_mul_coarseSquare_eqv
    (S : SlabScalePair) (rowCeiling columnCeiling g : Q') :
    (((rowCeiling * (g * g)) *
          positiveExpandedReceiverFiberPartitionDensity S +
        (columnCeiling * (g * g)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)) ≈
      (((rowCeiling + columnCeiling) * (g * g)) *
        coarseSquareCancelledCovarianceDenominator S) := by
  let density := positiveExpandedReceiverFiberPartitionDensity S
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  refine Q'.eqv_trans _
    ((((rowCeiling * (g * g)) + (columnCeiling * (g * g))) *
        density) * coarseSquare) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ coarseSquare
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (rowCeiling * (g * g)) (columnCeiling * (g * g)) density))
  refine Q'.eqv_trans _
    ((((rowCeiling + columnCeiling) * (g * g)) * density) *
      coarseSquare) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ coarseSquare
      (Q'.mul_eqv_congr_right _ _ density
        (Q'.eqv_symm
          (Q'.add_mul_eqv rowCeiling columnCeiling (g * g))))
  refine Q'.eqv_trans _
    (((rowCeiling + columnCeiling) * (g * g)) *
      (density * coarseSquare)) _
    (Q'.mul_assoc_eqv
      ((rowCeiling + columnCeiling) * (g * g)) density coarseSquare) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by
    simpa only [density, coarseSquare, fineSquare,
      coarseSquareCancelledCovarianceDenominator] using
        positiveExpandedReceiverFiberPartitionDensity_mul_coarseSquare_eqv S)

/-! ## 2. Per-scale relative estimates sum without volume loss -/

/-- One connected-row aggregate and one combined posterior-sector aggregate
imply the full dimensionless three-term budget.  This is the preferred
interface: the analytic posterior estimate need not split between sectors. -/
theorem splitPosteriorColumnBudget_le_combinedAggregateRelativeWeights
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hcolumns :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      let disconnected :=
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          (listQSum connected.targetWeight connected.targets +
            listQSum disconnected.targetWeight disconnected.targets)) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ coarseSquare := by
    simpa only [S, root, target, htarget, connected, coarseSquare] using
      connectedDensityTransport_sourceWeight_le_coarseSquare
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤
        coarseSquare := by
    simpa only [S, root, target, htarget, connected, disconnected,
      coarseSquare] using
      splitDensityTransports_targetWeight_le_coarseSquare
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hbudget :
      (Q'.abs connected.rowCoefficientDefect +
          connected.posteriorColumnCoefficientL1) +
        disconnected.posteriorColumnCoefficientL1 ≤
      (rowRelative + columnRelative) * coarseSquare :=
    connected.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_combinedAggregate
      disconnected rowRelative columnRelative coarseSquare
      hrowRelative hcolumnRelative
      (by simpa only [S, root, target, htarget, connected] using hrow)
      (by simpa only [S, root, target, htarget, connected, disconnected] using
        hcolumns)
      hsourceMass htargetMass
  refine Q'.le_trans' _ _ _ ?_ hbudget
  exact Q'.le_of_eqv (by
    unfold actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
    simp only [S, root, target, connected, disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1]
    apply Q'.eqv_of_eq
    congr <;> apply Subsingleton.elim)

/-- The preferred receiver-column statement uses one literal `l1` sum and
one physical mass on the original full four-cell target carrier. -/
theorem splitPosteriorColumnBudget_le_fullCarrierRelativeWeights
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hcolumns :
      let S := schedule.scalePair scale
      let root := (schedule.faceMap scale).coarseRoot
      let target := (schedule.faceMap scale).coarseTarget
      let htarget := (schedule.faceMap scale).coarseTarget_mem
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget ≤
        columnRelative *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target)) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let fullL1 :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let fullMass :=
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target)
  have hl1 :
      fullL1 ≈
        connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 := by
    simpa only [S, root, target, htarget, connected, disconnected, fullL1]
      using
        actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_eqv_split
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hmass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≈
        fullMass := by
    simpa only [S, root, target, htarget, connected, disconnected, fullMass]
      using
        splitDensityTransports_targetWeight_eqv_fourCellTargetWeight
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hcombined :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          (listQSum connected.targetWeight connected.targets +
            listQSum disconnected.targetWeight disconnected.targets) := by
    refine Q'.le_trans' _ fullL1 _ (Q'.le_of_eqv (Q'.eqv_symm hl1)) ?_
    refine Q'.le_trans' _ (columnRelative * fullMass) _
      (by simpa only [S, root, target, htarget, fullL1, fullMass] using
        hcolumns) ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left columnRelative _ _ (Q'.eqv_symm hmass))
  exact splitPosteriorColumnBudget_le_combinedAggregateRelativeWeights
    schedule scale rowRelative columnRelative
    hrowRelative hcolumnRelative
    (by simpa only [S, root, target, htarget, connected] using hrow)
    (by simpa only [S, root, target, htarget, connected, disconnected] using
      hcombined)

/-- A ceiling on the single total normalized full-carrier posterior cost is
equivalent to the preferred aggregate column input, including when the target
carrier is empty. -/
theorem splitPosteriorColumnBudget_le_fullCarrierRelativeCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hcolumnCost :
      let S := schedule.scalePair scale
      let root := (schedule.faceMap scale).coarseRoot
      let target := (schedule.faceMap scale).coarseTarget
      let htarget := (schedule.faceMap scale).coarseTarget_mem
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget ≤
        columnRelative) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  have hcolumns :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_of_relativeCost_le
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
      columnRelative
      (by simpa only [S, root, target, htarget] using hcolumnCost)
  exact splitPosteriorColumnBudget_le_fullCarrierRelativeWeights
    schedule scale rowRelative columnRelative
    hrowRelative hcolumnRelative
    (by simpa only [S, root, target, htarget] using hrow)
    (by simpa only [S, root, target, htarget,
        actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass]
      using hcolumns)

/-- A bound on the explicit connected-row density `l1` budget is a sufficient
row input for the preferred full-carrier posterior compiler. -/
theorem splitPosteriorColumnBudget_le_fullCarrierRelativeDensityL1
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrowL1 :
      let S := schedule.scalePair scale
      let root := (schedule.faceMap scale).coarseRoot
      let target := (schedule.faceMap scale).coarseTarget
      let htarget := (schedule.faceMap scale).coarseTarget_mem
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hcolumns :
      let S := schedule.scalePair scale
      let root := (schedule.faceMap scale).coarseRoot
      let target := (schedule.faceMap scale).coarseTarget
      let htarget := (schedule.faceMap scale).coarseTarget_mem
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
          S rfl (schedule.effectiveCoupling_pos scale) root target htarget ≤
        columnRelative *
          listQSum (slabObservableTwoReplicaPairWeight S.coarse)
            (slabObservableFourCellTargetPairs S.coarse root target)) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hrow :
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources := by
    refine Q'.le_trans' _
      (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDefectL1
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget) _ ?_ ?_
    · simpa only [connected,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt]
        using
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt_abs_le_densityDefectL1
            S rfl (schedule.effectiveCoupling_pos scale) root target htarget
    · simpa only [S, root, target, htarget, connected] using hrowL1
  exact splitPosteriorColumnBudget_le_fullCarrierRelativeWeights
    schedule scale rowRelative columnRelative
    hrowRelative hcolumnRelative
    (by simpa only [S, root, target, htarget, connected] using hrow)
    (by simpa only [S, root, target, htarget] using hcolumns)

/-- Separate posterior-sector aggregates compile to the weaker combined
posterior interface. -/
theorem splitPosteriorColumnBudget_le_aggregateRelativeWeights
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hconnectedColumn :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      connected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum connected.targetWeight connected.targets)
    (hdisconnectedColumn :
      let S := schedule.scalePair scale
      let disconnected :=
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum disconnected.targetWeight disconnected.targets) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hcolumns :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          (listQSum connected.targetWeight connected.targets +
            listQSum disconnected.targetWeight disconnected.targets) := by
    refine Q'.le_trans' _
      (columnRelative * listQSum connected.targetWeight connected.targets +
        columnRelative *
          listQSum disconnected.targetWeight disconnected.targets) _
      (Q'.add_le_add
        (by simpa only [S, root, target, htarget, connected] using
          hconnectedColumn)
        (by simpa only [S, root, target, htarget, disconnected] using
          hdisconnectedColumn)) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_add_eqv columnRelative
          (listQSum connected.targetWeight connected.targets)
          (listQSum disconnected.targetWeight disconnected.targets)))
  exact splitPosteriorColumnBudget_le_combinedAggregateRelativeWeights
    schedule scale rowRelative columnRelative
    hrowRelative hcolumnRelative
    (by simpa only [S, root, target, htarget, connected] using hrow)
    (by simpa only [S, root, target, htarget, connected, disconnected] using
      hcolumns)

/-- Source- and target-relative inputs bound the full dimensionless
three-term posterior budget by the sum of their two relative constants times
the coarse partition square.  This stronger pointwise route is retained as an
adapter to the aggregate theorem. -/
theorem splitPosteriorColumnBudget_le_relativeWeights
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (rowRelative columnRelative : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrow :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ source, source ∈ connected.sources →
        Q'.abs
            (connected.sourceCoefficient source *
              ((1 : Q') + -connected.rowMass source)) ≤ rowRelative)
    (hconnectedColumn :
      let S := schedule.scalePair scale
      let connected :=
        actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ target, target ∈ connected.targets →
        Q'.abs
            (connected.transportedSourceCoefficientColumnMass target -
              connected.targetWeight target *
                connected.targetCoefficient target) ≤
          columnRelative * connected.targetWeight target)
    (hdisconnectedColumn :
      let S := schedule.scalePair scale
      let disconnected :=
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem
      ∀ target, target ∈ disconnected.targets →
        Q'.abs
            (disconnected.transportedSourceCoefficientColumnMass target -
              disconnected.targetWeight target *
                disconnected.targetCoefficient target) ≤
          columnRelative * disconnected.targetWeight target) :
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
        schedule scale ≤
      (rowRelative + columnRelative) *
        ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hsourceWeight : ∀ source, source ∈ connected.sources →
      (0 : Q') ≤ connected.sourceWeight source := by
    intro source _
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport]
      using slabObservableTwoReplicaPairWeight_nonnegative
        S.coarse root source.1
  have hrowAggregate :
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources :=
    connected.rowCoefficientDefect_abs_le_relativeSourceWeight
      rowRelative hsourceWeight
      (by simpa only [S, root, target, htarget, connected] using hrow)
  have hconnectedAggregate :
      connected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum connected.targetWeight connected.targets :=
    connected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative
      (by simpa only [S, root, target, htarget, connected] using
        hconnectedColumn)
  have hdisconnectedAggregate :
      disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum disconnected.targetWeight disconnected.targets :=
    disconnected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative
      (by simpa only [S, root, target, htarget, disconnected] using
        hdisconnectedColumn)
  exact splitPosteriorColumnBudget_le_aggregateRelativeWeights
    schedule scale rowRelative columnRelative
    hrowRelative hcolumnRelative
    (by simpa only [S, root, target, htarget, connected] using hrowAggregate)
    (by simpa only [S, root, target, htarget, connected] using
      hconnectedAggregate)
    (by simpa only [S, root, target, htarget, disconnected] using
      hdisconnectedAggregate)

/-! ## 3. Matched-AF local inputs compile to the existing global bridge -/

/-- Preferred coverage-insensitive matched-AF input.  Its only receiver
analytic obligation is one full-source plus full-target density-coefficient
`l1` estimate at coupling-square order. -/
structure MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coefficientL1QuadraticCeiling : Q'
  coefficientL1QuadraticCeiling_pos :
    (0 : Q') < coefficientL1QuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  fullCoefficientL1_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
          S rfl (schedule.effectiveCoupling_pos scale) root target +
        actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coefficientL1QuadraticCeiling *
          (coupling scale * coupling scale)) *
        coarseSquareCancelledCovarianceDenominator S

namespace MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

/-- The aggregate coefficient calibration feeds the established matched-AF
three-budget compiler without introducing separate row or posterior fields. -/
def toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
    (control :
      MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  connectedQuadraticCeiling := control.coefficientL1QuadraticCeiling
  connectedQuadraticCeiling_pos := control.coefficientL1QuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  posteriorColumn_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    exact Q'.le_trans' _ _ _
      (splitPosteriorColumnBudget_le_fullCoefficientL1Raw schedule scale)
      (by simpa only [schedule] using
        control.fullCoefficientL1_quadratic_le scale hscale)

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl

/-- A volume-safe matched-AF posterior adapter retaining separate connected
row and normalized posterior-cost inputs. -/
structure MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  rowQuadraticCeiling : Q'
  rowQuadraticCeiling_pos : (0 : Q') < rowQuadraticCeiling
  posteriorQuadraticCeiling : Q'
  posteriorQuadraticCeiling_pos : (0 : Q') < posteriorQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  connectedRow_aggregateRelative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    Q'.abs connected.rowCoefficientDefect ≤
      ((rowQuadraticCeiling * (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
        listQSum connected.sourceWeight connected.sources
  posteriorColumn_relativeCost : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    let htarget := (schedule.faceMap scale).coarseTarget_mem
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget ≤
      (posteriorQuadraticCeiling * (coupling scale * coupling scale)) *
        positiveExpandedReceiverFiberPartitionDensity S

namespace MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

def connectedQuadraticCeiling
    (control :
      MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  control.rowQuadraticCeiling + control.posteriorQuadraticCeiling

theorem connectedQuadraticCeiling_pos
    (control :
      MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.connectedQuadraticCeiling :=
  Q'.add_pos control.rowQuadraticCeiling_pos
    control.posteriorQuadraticCeiling_pos

/-- Compile the aggregate sector-relative estimates into the already checked
global matched-AF posterior-cost interface. -/
def toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
    (control :
      MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  connectedQuadraticCeiling := control.connectedQuadraticCeiling
  connectedQuadraticCeiling_pos := control.connectedQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  posteriorColumn_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let g2 := coupling scale * coupling scale
    let density := positiveExpandedReceiverFiberPartitionDensity S
    let rowRelative := (control.rowQuadraticCeiling * g2) * density
    let columnRelative :=
      (control.posteriorQuadraticCeiling * g2) * density
    have hg2 : (0 : Q') ≤ g2 :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (coupling_pos scale))
        (Q'.le_of_lt (coupling_pos scale))
    have hdensity : (0 : Q') ≤ density :=
      Q'.le_of_lt (positiveExpandedReceiverFiberPartitionDensity_pos S)
    have hrowRelative : (0 : Q') ≤ rowRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.rowQuadraticCeiling_pos) hg2)
        hdensity
    have hcolumnRelative : (0 : Q') ≤ columnRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.posteriorQuadraticCeiling_pos) hg2)
        hdensity
    have hlocal := splitPosteriorColumnBudget_le_fullCarrierRelativeCost
      schedule scale rowRelative columnRelative
      hrowRelative hcolumnRelative
      (by simpa only [schedule, S, g2, density, rowRelative] using
        control.connectedRow_aggregateRelative scale hscale)
      (by simpa only [schedule, S, g2, density, columnRelative] using
        control.posteriorColumn_relativeCost scale hscale)
    exact Q'.le_trans' _ _ _ hlocal
      (Q'.le_of_eqv (by
        simpa only [schedule, S, g2, density, rowRelative, columnRelative,
          connectedQuadraticCeiling] using
          relativeQuadraticBudget_mul_coarseSquare_eqv
            S control.rowQuadraticCeiling
              control.posteriorQuadraticCeiling (coupling scale)))

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl

/-- A volume-safe refinement of the matched-AF posterior input.  The global
posterior estimate is replaced by one connected-row relative estimate and one
common target-weight-relative estimate on each complementary target sector. -/
structure MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  rowQuadraticCeiling : Q'
  rowQuadraticCeiling_pos : (0 : Q') < rowQuadraticCeiling
  posteriorQuadraticCeiling : Q'
  posteriorQuadraticCeiling_pos : (0 : Q') < posteriorQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  connectedRow_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ source, source ∈ connected.sources →
      Q'.abs
          (connected.sourceCoefficient source *
            ((1 : Q') + -connected.rowMass source)) ≤
        (rowQuadraticCeiling * (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S
  connectedColumn_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let connected :=
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ target, target ∈ connected.targets →
      Q'.abs
          (connected.transportedSourceCoefficientColumnMass target -
            connected.targetWeight target *
              connected.targetCoefficient target) ≤
        ((posteriorQuadraticCeiling *
            (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
            connected.targetWeight target
  disconnectedColumn_relative : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let disconnected :=
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem
    ∀ target, target ∈ disconnected.targets →
      Q'.abs
          (disconnected.transportedSourceCoefficientColumnMass target -
            disconnected.targetWeight target *
              disconnected.targetCoefficient target) ≤
        ((posteriorQuadraticCeiling *
            (coupling scale * coupling scale)) *
          positiveExpandedReceiverFiberPartitionDensity S) *
            disconnected.targetWeight target

namespace MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

def connectedQuadraticCeiling
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) : Q' :=
  control.rowQuadraticCeiling + control.posteriorQuadraticCeiling

theorem connectedQuadraticCeiling_pos
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    (0 : Q') < control.connectedQuadraticCeiling :=
  Q'.add_pos control.rowQuadraticCeiling_pos
    control.posteriorQuadraticCeiling_pos

/-- Sum the local relative estimates and feed the previously verified global
matched-AF posterior bridge. -/
def toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  connectedQuadraticCeiling := control.connectedQuadraticCeiling
  connectedQuadraticCeiling_pos := control.connectedQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  posteriorColumn_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let g2 := coupling scale * coupling scale
    let density := positiveExpandedReceiverFiberPartitionDensity S
    let rowRelative := (control.rowQuadraticCeiling * g2) * density
    let columnRelative :=
      (control.posteriorQuadraticCeiling * g2) * density
    have hg2 : (0 : Q') ≤ g2 :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (coupling_pos scale))
        (Q'.le_of_lt (coupling_pos scale))
    have hdensity : (0 : Q') ≤ density :=
      Q'.le_of_lt (positiveExpandedReceiverFiberPartitionDensity_pos S)
    have hrowRelative : (0 : Q') ≤ rowRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.rowQuadraticCeiling_pos) hg2)
        hdensity
    have hcolumnRelative : (0 : Q') ≤ columnRelative :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt control.posteriorQuadraticCeiling_pos) hg2)
        hdensity
    have hlocal := splitPosteriorColumnBudget_le_relativeWeights
      schedule scale rowRelative columnRelative
      hrowRelative hcolumnRelative
      (by simpa only [schedule, S, g2, density, rowRelative] using
        control.connectedRow_relative scale hscale)
      (by simpa only [schedule, S, g2, density, columnRelative] using
        control.connectedColumn_relative scale hscale)
      (by simpa only [schedule, S, g2, density, columnRelative] using
        control.disconnectedColumn_relative scale hscale)
    exact Q'.le_trans' _ _ _ hlocal
      (Q'.le_of_eqv (by
        simpa only [schedule, S, g2, density, rowRelative, columnRelative,
          connectedQuadraticCeiling] using
          relativeQuadraticBudget_mul_coarseSquare_eqv
            S control.rowQuadraticCeiling
              control.posteriorQuadraticCeiling (coupling scale)))

theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl

#print axioms slabObservableFourCellTargetPairs_weight_le_partitionSquare
#print axioms connectedDensityTransport_sourceWeight_le_coarseSquare
#print axioms splitDensityTransports_targetWeight_le_coarseSquare
#print axioms positiveExpandedReceiverFiberPartitionDensity_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt_abs_le_densityDefectL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullSourceDensityCoefficientL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullTargetDensityCoefficientL1
#print axioms splitDensityTransports_sourceCoefficientL1_eqv_full
#print axioms splitDensityTransports_targetCoefficientL1_eqv_full
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorDensityBudget_le_fullCoefficientL1
#print axioms splitPosteriorColumnBudget_le_fullCoefficientL1Raw
#print axioms splitPosteriorColumnBudget_le_fullCoefficientL1
#print axioms splitPosteriorColumnBudget_le_combinedAggregateRelativeWeights
#print axioms splitPosteriorColumnBudget_le_fullCarrierRelativeWeights
#print axioms splitPosteriorColumnBudget_le_fullCarrierRelativeCost
#print axioms splitPosteriorColumnBudget_le_fullCarrierRelativeDensityL1
#print axioms splitPosteriorColumnBudget_le_aggregateRelativeWeights
#print axioms splitPosteriorColumnBudget_le_relativeWeights
#print axioms MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
#print axioms MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl.connectedQuadraticCeiling
#print axioms MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl.connectedQuadraticCeiling_pos
#print axioms MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnFullCarrierRelativeQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.connectedQuadraticCeiling
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.connectedQuadraticCeiling_pos
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnRelativeQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnRelativeQuadraticCost
