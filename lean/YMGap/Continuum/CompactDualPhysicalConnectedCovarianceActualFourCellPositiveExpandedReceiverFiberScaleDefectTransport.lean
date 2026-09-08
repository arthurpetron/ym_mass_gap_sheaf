/-
# Receiver-column transport of the partition-scaled covariance coefficient

The exact receiver-fiber scale defect is a signed coefficient mass on the
coarse source and target pair carriers.  This module puts that coefficient
field through the same source-dependent successful posterior kernel used by
the paired aggregate transport.

The resulting cross splits exactly into three analytic debts:

* coefficient mass lost by incomplete source rows;
* coefficient variation along successful source-choice edges;
* mismatch between the realized incoming coefficient columns and the target
  coefficient mass.

This is an identity, not an estimate.  No bound on any of the three debts is
asserted here, and therefore no `O(a)` estimate, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Clay conclusion is claimed.

Constructive contract: finite lists and exact `Q'` identities only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientTransport
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
import YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance scaleDefectTransportPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

abbrev Receiver (S : SlabScalePair) (root : Nat) :=
  SlabObservableTwoReplicaPair S.coarse root

/-- The actual scaled receiver coefficient field, equipped with the successful
posterior kernel already present in the paired aggregate transport. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    FiniteDependentCoefficientTransport (Receiver S root) (Receiver S root) :=
  { sources := slabObservableFourCellSourcePairs S.coarse root target
    sourceWeight := slabObservableTwoReplicaPairWeight S.coarse
    sourceCoefficient :=
      positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target
    rowMass := data.rowMass
    targets := slabObservableFourCellTargetPairs S.coarse root target
    targets_nodup :=
      slabObservableFourCellTargetPairs_nodup S.coarse root target
    targetWeight := slabObservableTwoReplicaPairWeight S.coarse
    targetCoefficient :=
      positiveExpandedFourCellTargetReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target
    Choice := data.Choice
    choices := data.choices
    localWeight := data.localWeight
    realize := data.realize
    coverage := data.coverage
    row_mass := data.row_mass }

def actualPositiveExpandedReceiverFiberScaleDefectRowDebt
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    S hfineCutoff hcoarseCoupling root target data).rowCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    S hfineCutoff hcoarseCoupling root target data).edgeCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    S hfineCutoff hcoarseCoupling root target data).columnCoefficientDefect

theorem actualScaleDefectTransport_sourceCoefficientMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
        S hfineCutoff hcoarseCoupling root target data).sourceCoefficientMass ≈
      positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    FiniteDependentCoefficientTransport.sourceCoefficientMass
    positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_comm_eqv _ _

theorem actualScaleDefectTransport_targetCoefficientMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
        S hfineCutoff hcoarseCoupling root target data).targetCoefficientMass ≈
      positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
    FiniteDependentCoefficientTransport.targetCoefficientMass
    positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_comm_eqv _ _

/-- The actual partition-scaled cross is exactly the sum of its row, edge, and
column transport debts. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_threeDebts
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (actualPositiveExpandedReceiverFiberScaleDefectRowDebt
          S hfineCutoff hcoarseCoupling root target data +
        actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
          S hfineCutoff hcoarseCoupling root target data) +
        actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
          S hfineCutoff hcoarseCoupling root target data := by
  let transport :=
    actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
      S hfineCutoff hcoarseCoupling root target data
  refine Q'.eqv_trans _
    (transport.sourceCoefficientMass - transport.targetCoefficientMass) _ ?_ ?_
  · unfold actualPositiveExpandedReceiverFiberScaleDefectCross
    exact sub_eqv_both_local
      (Q'.eqv_symm
        (actualScaleDefectTransport_sourceCoefficientMass_eqv
          S hfineCutoff hcoarseCoupling root target data))
      (Q'.eqv_symm
        (actualScaleDefectTransport_targetCoefficientMass_eqv
          S hfineCutoff hcoarseCoupling root target data))
  · exact transport.coefficientCross_eqv_row_add_edge_add_column

/-- Triangle control for the actual scaled coefficient cross.  Later analytic
work must bound the three displayed terms separately and uniformly in scale. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_threeDebts
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    Q'.abs (actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling root target) ≤
      (Q'.abs (actualPositiveExpandedReceiverFiberScaleDefectRowDebt
          S hfineCutoff hcoarseCoupling root target data) +
        Q'.abs (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
          S hfineCutoff hcoarseCoupling root target data)) +
        Q'.abs (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
          S hfineCutoff hcoarseCoupling root target data) := by
  have hsplit :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_threeDebts
      S hfineCutoff hcoarseCoupling root target data
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (actualPositiveExpandedReceiverFiberScaleDefectRowDebt
          S hfineCutoff hcoarseCoupling root target data +
        actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
          S hfineCutoff hcoarseCoupling root target data)
      (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
        S hfineCutoff hcoarseCoupling root target data))
    (Q'.add_le_add
      (Q'.abs_add_le'
        (actualPositiveExpandedReceiverFiberScaleDefectRowDebt
          S hfineCutoff hcoarseCoupling root target data)
        (actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
          S hfineCutoff hcoarseCoupling root target data))
      (Q'.le_refl'
        (Q'.abs (actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
          S hfineCutoff hcoarseCoupling root target data))))

/-- The middle debt is the literal successful-edge coefficient variation. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_variation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun source => slabObservableTwoReplicaPairWeight S.coarse source *
          listQSum
            (fun choice =>
              (positiveExpandedFourCellSourceReceiverFiberScaleDefect
                    S hfineCutoff hcoarseCoupling root target source -
                positiveExpandedFourCellTargetReceiverFiberScaleDefect
                    S hfineCutoff hcoarseCoupling root target
                    (data.realize source choice)) *
                data.localWeight source choice)
            (data.choices source))
        (slabObservableFourCellSourcePairs S.coarse root target) := by
  exact
    FiniteDependentCoefficientTransport.edgeCoefficientDefect_eqv_variation
      (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
        S hfineCutoff hcoarseCoupling root target data)

/-- The transported part of the column debt is grouped on the literal common
receiver columns, exposing the incoming successful weight at each target. -/
theorem actualScaleDefectTransport_transportedTargetCoefficientMass_eqv_columns
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    FiniteDependentCoefficientTransport.transportedTargetCoefficientMass
        (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
          S hfineCutoff hcoarseCoupling root target data) ≈
      listQSum
        (fun receiver =>
          listQSum
              (fun source =>
                slabObservableTwoReplicaPairWeight S.coarse source *
                  dependentKernelPushforwardWeight
                    data.Choice data.choices data.localWeight data.realize
                    source receiver)
              (slabObservableFourCellSourcePairs S.coarse root target) *
            positiveExpandedFourCellTargetReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  exact
    FiniteDependentCoefficientTransport.transportedTargetCoefficientMass_eqv_columns
      (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
        S hfineCutoff hcoarseCoupling root target data)

#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowDebt
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
#print axioms actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
#print axioms actualScaleDefectTransport_sourceCoefficientMass_eqv
#print axioms actualScaleDefectTransport_targetCoefficientMass_eqv
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_threeDebts
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_threeDebts
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_variation
#print axioms actualScaleDefectTransport_transportedTargetCoefficientMass_eqv_columns

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
