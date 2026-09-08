/-
# Receiver-column transport of the partition-scaled covariance coefficient

The exact receiver-fiber scale defect is a signed coefficient mass on the
coarse source and target pair carriers.  Conditional on a
`SlabObservablePairedAggregatePosteriorTransport`, this module puts that
coefficient field through its source-dependent successful posterior kernel.

The resulting cross splits exactly into three analytic debts:

* coefficient mass lost by incomplete source rows;
* coefficient variation along successful source-choice edges;
* mismatch between the realized incoming coefficient columns and the target
  coefficient mass.

This is an identity, not an estimate or a construction of that posterior
interface.  No repository module currently inhabits the complete-cell
posterior parameter used here.  The fixed-anchor guarded aggregate theorem is
not a schedule-level instance.  No bound on any of the three debts is asserted
here, and therefore no `O(a)` estimate, continuum measure, OS/GNS
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
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance scaleDefectTransportPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem bool_eq_false_of_not_eq_true_local
    (value : Bool) (hvalue : (!value) = true) : value = false := by
  cases value <;> simp_all

private theorem listQSum_eqv_zero_of_pointwise_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

abbrev Receiver (S : SlabScalePair) (root : Nat) :=
  SlabObservableTwoReplicaPair S.coarse root

/-- The actual scaled receiver coefficient field, conditional on a supplied
complete-cell successful posterior kernel.  This definition does not construct
that kernel. -/
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

/-- The actual row debt is the scaled source coefficient times the unretained
mass of each posterior row. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_unretained
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight S.coarse source *
            (positiveExpandedFourCellSourceReceiverFiberScaleDefect
                S hfineCutoff hcoarseCoupling root target source *
              ((1 : Q') + -data.rowMass source)))
        (slabObservableFourCellSourcePairs S.coarse root target) := by
  exact
    FiniteDependentCoefficientTransport.rowCoefficientDefect_eqv_unretained
      (actualPositiveExpandedReceiverFiberScaleDefectCoefficientTransport
        S hfineCutoff hcoarseCoupling root target data)

/-- Full disconnected rows contribute exactly zero to the coefficient-weighted
unretained mass, irrespective of the sign of the scaled coefficient. -/
theorem actualScaleDefectUnretainedRowTerm_eqv_zero_of_disconnected
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target)
    (source : Receiver S root)
    (hsource : source ∈
      slabObservableFourCellSourcePairs S.coarse root target)
    (hdisconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        S.coarse root target source = false) :
    slabObservableTwoReplicaPairWeight S.coarse source *
        (positiveExpandedFourCellSourceReceiverFiberScaleDefect
            S hfineCutoff hcoarseCoupling root target source *
          ((1 : Q') + -data.rowMass source)) ≈ 0 := by
  have hrow := data.disconnected_row_mass source hsource hdisconnected
  have hcomplement : ((1 : Q') + -data.rowMass source) ≈ 0 := by
    refine Q'.eqv_trans _ ((1 : Q') + -(1 : Q')) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl 1)
        (Q'.neg_eqv_congr _ _ hrow)
    · exact Q'.add_neg_self_eqv 1
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairWeight S.coarse source *
      (positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target source * 0)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (slabObservableTwoReplicaPairWeight S.coarse source) _ _
      (Q'.mul_eqv_congr_left
        (positiveExpandedFourCellSourceReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target source) _ _ hcomplement)
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (slabObservableTwoReplicaPairWeight S.coarse source) _ _
        (Q'.mul_zero_eqv _))
      (Q'.mul_zero_eqv _)

/-- Consequently the row debt is supported only on the paired-support
connected source sector. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_connected
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight S.coarse source *
            (positiveExpandedFourCellSourceReceiverFiberScaleDefect
                S hfineCutoff hcoarseCoupling root target source *
              ((1 : Q') + -data.rowMass source)))
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) := by
  let term := fun source : Receiver S root =>
    slabObservableTwoReplicaPairWeight S.coarse source *
      (positiveExpandedFourCellSourceReceiverFiberScaleDefect
          S hfineCutoff hcoarseCoupling root target source *
        ((1 : Q') + -data.rowMass source))
  have hrow :=
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_unretained
      S hfineCutoff hcoarseCoupling root target data
  have hpartition :=
    listQSum_filter_partition term
      (fun source =>
        slabObservableTwoReplicaPairPairedSupportConnectedB
          S.coarse root target source)
      (slabObservableFourCellSourcePairs S.coarse root target)
  have hdisconnected :
      listQSum term
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            S.coarse root target) ≈ 0 := by
    apply listQSum_eqv_zero_of_pointwise_local
    intro source hsource
    have hparts := List.mem_filter.mp hsource
    have hfalse := bool_eq_false_of_not_eq_true_local
      (slabObservableTwoReplicaPairPairedSupportConnectedB
        S.coarse root target source) hparts.2
    exact actualScaleDefectUnretainedRowTerm_eqv_zero_of_disconnected
      S hfineCutoff hcoarseCoupling root target data source hparts.1 hfalse
  refine Q'.eqv_trans _ (listQSum term
    (slabObservableFourCellSourcePairs S.coarse root target)) _ hrow ?_
  refine Q'.eqv_trans _
    (listQSum term
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) +
      listQSum term
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          S.coarse root target)) _ ?_ ?_
  · simpa only [slabObservablePairedSupportConnectedFourCellSourcePairs,
      slabObservablePairedSupportSeparatedFourCellSourcePairs] using hpartition
  · refine Q'.eqv_trans _
      (listQSum term
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) + 0) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hdisconnected) ?_
    refine Q'.eqv_trans _
      (listQSum term
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target)) _
      (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
    exact Q'.eqv_refl _

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

/-- The actual column debt is the signed incoming column slack paired with the
target scaled coefficient.  The aggregate posterior certificate makes each
slack nonpositive, but a magnitude estimate still needs coefficient control. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_slack
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (data : SlabObservablePairedAggregatePosteriorTransport
      S.coarse root target) :
    actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
        S hfineCutoff hcoarseCoupling root target data ≈
      listQSum
        (fun receiver =>
          (listQSum
                (fun source =>
                  slabObservableTwoReplicaPairWeight S.coarse source *
                    dependentKernelPushforwardWeight
                      data.Choice data.choices data.localWeight data.realize
                      source receiver)
                (slabObservableFourCellSourcePairs
                  S.coarse root target) -
              slabObservableTwoReplicaPairWeight S.coarse receiver) *
            positiveExpandedFourCellTargetReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  exact
    FiniteDependentCoefficientTransport.columnCoefficientDefect_eqv_slack
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
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_unretained
#print axioms actualScaleDefectUnretainedRowTerm_eqv_zero_of_disconnected
#print axioms actualPositiveExpandedReceiverFiberScaleDefectRowDebt_eqv_connected
#print axioms actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt_eqv_variation
#print axioms actualScaleDefectTransport_transportedTargetCoefficientMass_eqv_columns
#print axioms actualPositiveExpandedReceiverFiberScaleDefectColumnDebt_eqv_slack

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
