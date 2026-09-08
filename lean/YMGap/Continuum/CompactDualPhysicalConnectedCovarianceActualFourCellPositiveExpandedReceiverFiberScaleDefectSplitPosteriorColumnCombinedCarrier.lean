/-
# Reassemble the split posterior columns on the full target carrier

The connected and disconnected receiver transports land in complementary
Boolean filters of the same opposite four-cell target carrier.  Their two
posterior-column `l1` sums can therefore be presented as one literal sum over
that full carrier, selecting the appropriate transport column by the same
Boolean predicate.  Their target masses reassemble in exactly the same way.

This is an exact finite reindexing only.  It proves no smallness estimate,
spacing comparison, continuum limit, OS/GNS reconstruction, Hamiltonian gap,
or Clay conclusion.

Constructive contract: finite rational sums and Boolean case analysis only;
no choice, `Classical`, `native_decide`, proof hole, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
import YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance combinedCarrierPairDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

/-- The absolute posterior mismatch at one full-carrier receiver, using the
connected or disconnected transport selected by its support sector. -/
def actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (receiver : Receiver S root) : Q' :=
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  if slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver then
    Q'.abs
      (connected.transportedSourceCoefficientColumnMass receiver -
        connected.targetWeight receiver *
          connected.targetCoefficient receiver)
  else
    Q'.abs
      (disconnected.transportedSourceCoefficientColumnMass receiver -
        disconnected.targetWeight receiver *
          disconnected.targetCoefficient receiver)

/-- The two split posterior-column sums written as one sum over the original
opposite four-cell target carrier. -/
def actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  listQSum
    (actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm
      S hfineCutoff hcoarseCoupling root target htarget)
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- Boolean target-sector partition reassembles the posterior `l1` costs
exactly, without a triangle inequality or a carrier-cardinality factor. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_eqv_split
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
        S hfineCutoff hcoarseCoupling root target htarget ≈
      (actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
          S hfineCutoff hcoarseCoupling root target htarget
        ).posteriorColumnCoefficientL1 +
      (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
          S hfineCutoff hcoarseCoupling root target htarget
        ).posteriorColumnCoefficientL1 := by
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let sector := fun receiver : Receiver S root =>
    slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver
  let term :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm
      S hfineCutoff hcoarseCoupling root target htarget
  have hpartition :=
    listQSum_filter_partition term sector
      (slabObservableFourCellTargetPairs S.coarse root target)
  refine Q'.eqv_trans _
    (listQSum term connected.targets +
      listQSum term disconnected.targets) _ ?_ ?_
  · simpa only [connected, disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
      FiniteDependentCoefficientTransport.replaceCoefficients,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport,
      slabObservablePairedSupportConnectedFourCellTargetPairs,
      slabObservablePairedSupportDisconnectedFourCellTargetPairs, sector,
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1,
      term] using hpartition
  · apply Q'.add_eqv_congr'
    · unfold posteriorColumnCoefficientL1
      apply listQSum_congr_on
      intro receiver hreceiver
      have hsector : sector receiver = true :=
        (List.mem_filter.mp hreceiver).2
      simp only [term,
        actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm,
        sector, hsector, if_true]
      exact Q'.eqv_refl _
    · unfold posteriorColumnCoefficientL1
      apply listQSum_congr_on
      intro receiver hreceiver
      have hsectorNot : (!sector receiver) = true :=
        (List.mem_filter.mp hreceiver).2
      have hsector : sector receiver = false := by
        cases hvalue : sector receiver with
        | false => rfl
        | true =>
            simp only [hvalue, Bool.not_true, Bool.false_eq_true] at hsectorNot
      simp only [term,
        actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm,
        sector, hsector, Bool.false_eq_true, if_false]
      exact Q'.eqv_refl _

/-- The target weights of the two density transports reassemble to the
physical weight of the original full four-cell target carrier. -/
theorem splitDensityTransports_targetWeight_eqv_fourCellTargetWeight
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
        listQSum disconnected.targetWeight disconnected.targets ≈
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  dsimp only
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport,
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport,
    FiniteDependentCoefficientTransport.replaceCoefficients,
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
    using Q'.eqv_symm
      (slabObservableFourCellTargetPairs_pairedSupport_partition
        S.coarse root target)

#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityTerm
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_eqv_split
#print axioms splitDensityTransports_targetWeight_eqv_fourCellTargetWeight

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier
