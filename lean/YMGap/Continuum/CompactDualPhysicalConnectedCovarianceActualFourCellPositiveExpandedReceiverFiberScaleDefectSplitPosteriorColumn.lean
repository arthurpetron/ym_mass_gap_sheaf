/-
# Posterior-column compression of the actual split receiver transport

The explicit connected/disconnected receiver transport previously exposed
five surviving coefficient debts: three on the connected branch and two on
the disconnected branch.  Applying coefficient-weighted finite Fubini before
comparing with the target field combines each branch's edge and ordinary
column debts into one literal posterior-column mismatch.

For the actual positive accepted-fiber recoupling kernels this gives the exact
three-debt identity

```text
receiver scale-defect cross
  = connected row loss
      + connected posterior-column mismatch
      + disconnected posterior-column mismatch.
```

The module also proves the corresponding three-term `l1` majorant, including
the physical coarse--fine partition factor consumed by the covariance route.
No smallness estimate for these posterior mismatches is supplied.  In
particular, this is a finite posterior-column reduction, not a uniform
normalized-cost bound, physical gap floor, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: exact finite rational Fubini and triangle inequalities
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientPosterior
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumn

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance splitPosteriorColumnPairDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

/-! ## 1. The two literal posterior columns -/

def actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientL1

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientL1

/-! ## 2. Five algebraic debts collapse exactly to three -/

/-- The actual scale-defect cross is one connected row loss plus the two
coefficient-weighted posterior-column mismatches. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitThreePosteriorDebts
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
          S hfineCutoff hcoarseCoupling root target htarget +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) +
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
        S hfineCutoff hcoarseCoupling root target htarget := by
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hfive :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitFiveDebts
      S hfineCutoff hcoarseCoupling root target htarget
  have hconnected :
      ((actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) ≈
        actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
            S hfineCutoff hcoarseCoupling root target htarget := by
    exact Q'.eqv_trans _ _ _
      (by
        simpa only [connected,
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt,
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt,
          actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt]
          using
            (Q'.eqv_symm
              connected.coefficientCross_eqv_row_add_edge_add_column))
      (by
        simpa only [connected,
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt,
          actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt]
          using connected.coefficientCross_eqv_row_add_posteriorColumn)
  have hzero : disconnected.rowCoefficientDefect ≈ 0 := by
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt]
      using
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt_eqv_zero
          S hfineCutoff hcoarseCoupling root target htarget)
  have hdisconnectedEdgeColumnToCross :
      disconnected.edgeCoefficientDefect + disconnected.columnCoefficientDefect ≈
        disconnected.sourceCoefficientMass -
          disconnected.targetCoefficientMass := by
    refine Q'.eqv_trans _
      ((0 + disconnected.edgeCoefficientDefect) +
        disconnected.columnCoefficientDefect) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (Q'.eqv_of_eq
            (Q'.zero_add' disconnected.edgeCoefficientDefect)))
    refine Q'.eqv_trans _
      ((disconnected.rowCoefficientDefect +
          disconnected.edgeCoefficientDefect) +
        disconnected.columnCoefficientDefect) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hzero))
    exact Q'.eqv_symm
      disconnected.coefficientCross_eqv_row_add_edge_add_column
  have hdisconnectedCrossToPosterior :
      disconnected.sourceCoefficientMass -
          disconnected.targetCoefficientMass ≈
        disconnected.posteriorColumnCoefficientDefect := by
    refine Q'.eqv_trans _
      (disconnected.rowCoefficientDefect +
        disconnected.posteriorColumnCoefficientDefect) _
      disconnected.coefficientCross_eqv_row_add_posteriorColumn ?_
    refine Q'.eqv_trans _
      (0 + disconnected.posteriorColumnCoefficientDefect) _
      (Q'.add_eqv_congr_right _ _ _ hzero) ?_
    exact Q'.eqv_of_eq
      (Q'.zero_add' disconnected.posteriorColumnCoefficientDefect)
  have hdisconnected :
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget +
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget ≈
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
        S hfineCutoff hcoarseCoupling root target htarget := by
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt]
      using Q'.eqv_trans _ _ _
        hdisconnectedEdgeColumnToCross hdisconnectedCrossToPosterior
  exact Q'.eqv_trans _ _ _ hfive
    (Q'.add_eqv_congr' hconnected hdisconnected)

def actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (Q'.abs
      (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
        S hfineCutoff hcoarseCoupling root target htarget) +
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
      S hfineCutoff hcoarseCoupling root target htarget) +
  actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
    S hfineCutoff hcoarseCoupling root target htarget

theorem actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_splitPosteriorColumnL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let row :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      S hfineCutoff hcoarseCoupling root target htarget
  let connectedPosterior :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnectedPosterior :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
      S hfineCutoff hcoarseCoupling root target htarget
  have htriangle :
      Q'.abs
          (actualPositiveExpandedReceiverFiberScaleDefectCross
            S hfineCutoff hcoarseCoupling root target) ≤
        (Q'.abs row + Q'.abs connectedPosterior) +
          Q'.abs disconnectedPosterior := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitThreePosteriorDebts
            S hfineCutoff hcoarseCoupling root target htarget))) ?_
    exact Q'.le_trans' _ _ _
      (Q'.abs_add_le' (row + connectedPosterior) disconnectedPosterior)
      (Q'.add_le_add
        (Q'.abs_add_le' row connectedPosterior)
        (Q'.le_refl' (Q'.abs disconnectedPosterior)))
  have hconnectedPosterior :
      Q'.abs connectedPosterior ≤
        actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
          S hfineCutoff hcoarseCoupling root target htarget := by
    simpa only [connected, connectedPosterior,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1]
      using connected.posteriorColumnCoefficientDefect_abs_le_l1
  have hdisconnectedPosterior :
      Q'.abs disconnectedPosterior ≤
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
          S hfineCutoff hcoarseCoupling root target htarget := by
    simpa only [disconnected, disconnectedPosterior,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1]
      using disconnected.posteriorColumnCoefficientDefect_abs_le_l1
  exact Q'.le_trans' _ _ _ htriangle
    (by
      simpa only [row,
        actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1]
        using Q'.add_le_add
          (Q'.add_le_add
            (Q'.le_refl' (Q'.abs row)) hconnectedPosterior)
          hdisconnectedPosterior)

/-! ## 3. Schedule-level physical scaling -/

def actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.abs
      ((schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition) *
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem

theorem actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitPosteriorColumnBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectCross
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
        schedule scale := by
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let cross :=
    actualPositiveExpandedReceiverFiberScaleDefectCross
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
  let budget :=
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor cross)
    (by
      simpa only [factor, cross, budget,
        actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget]
        using Q'.mul_le_mul_of_nonneg_left
          (Q'.abs cross) budget (Q'.abs factor)
          (actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_splitPosteriorColumnL1
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem)
          (Q'.abs_nonneg factor))

#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitThreePosteriorDebts
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_splitPosteriorColumnL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
#print axioms actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitPosteriorColumnBudget

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumn
