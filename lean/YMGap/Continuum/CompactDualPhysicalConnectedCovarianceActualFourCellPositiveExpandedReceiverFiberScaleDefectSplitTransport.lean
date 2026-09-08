/-
# Split-sector transport of the receiver-fiber scale defect

The complete-cell aggregate posterior is not needed to obtain an explicit
coefficient transport.  The repository already contains two constructive
kernels on disjoint source and target sectors:

* the normalized support-disconnected switch;
* the canonically first-source-thinned support-connected switch.

This module specializes the generic dependent coefficient identity to both
kernels.  Exact Boolean partition of the source and target four-cells then
rewrites the complete receiver scale-defect cross as five debts.  The sixth
formal debt, the disconnected-row debt, vanishes because that row is exactly
normalized.

This removes the monolithic posterior object from the exact transport branch.
It proves no magnitude or refining-scale estimate for the five remaining
debts, no continuum measure, no OS/GNS reconstruction, no Hamiltonian gap,
and no Clay conclusion.

Constructive contract: explicit finite kernels and exact rational identities
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
import YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
import YMGap.Continuum.FiniteDependentKernelCoefficientTransport

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedTargetSectorSeparation
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem split_cross_local
    (connectedSource disconnectedSource connectedTarget disconnectedTarget : Q') :
    (connectedSource + disconnectedSource) -
        (connectedTarget + disconnectedTarget) ≈
      (connectedSource - connectedTarget) +
        (disconnectedSource - disconnectedTarget) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (connectedSource + disconnectedSource) _ _
      (Q'.neg_add_eqv connectedTarget disconnectedTarget)) ?_
  exact Q'.add_swap_inner
    connectedSource disconnectedSource (-connectedTarget) (-disconnectedTarget)

private theorem add_two_scaled_local
    (left right spacing denominator : Q') :
    (left * spacing) * denominator +
        (right * spacing) * denominator ≈
      ((left + right) * spacing) * denominator := by
  refine Q'.eqv_trans _
    ((left * spacing + right * spacing) * denominator) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (left * spacing) (right * spacing) denominator)
  · exact Q'.mul_eqv_congr_right _ _ denominator
      (Q'.eqv_symm (Q'.add_mul_eqv left right spacing))

private theorem add_three_scaled_local
    (first second third spacing denominator : Q') :
    ((first * spacing) * denominator +
        (second * spacing) * denominator) +
        (third * spacing) * denominator ≈
      (((first + second) + third) * spacing) * denominator := by
  refine Q'.eqv_trans _
    (((first + second) * spacing) * denominator +
      (third * spacing) * denominator) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (add_two_scaled_local first second spacing denominator)
  · exact add_two_scaled_local (first + second) third spacing denominator

private theorem add_five_scaled_local
    (first second third fourth fifth spacing denominator : Q') :
    (((first * spacing) * denominator +
          (second * spacing) * denominator) +
        (third * spacing) * denominator) +
      ((fourth * spacing) * denominator +
        (fifth * spacing) * denominator) ≈
      ((((first + second) + third) + (fourth + fifth)) * spacing) *
        denominator := by
  refine Q'.eqv_trans _
    ((((first + second) + third) * spacing) * denominator +
      ((fourth + fifth) * spacing) * denominator) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (add_three_scaled_local first second third spacing denominator)
      (add_two_scaled_local fourth fifth spacing denominator)
  · exact add_two_scaled_local
      ((first + second) + third) (fourth + fifth) spacing denominator

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

local instance splitTransportPairDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

/-! ## 1. The explicit disconnected coefficient transport -/

/-- The normalized support-disconnected switch, restricted to its exact
disconnected target sector. -/
def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    FiniteDependentCoefficientTransport
      (SlabObservablePairedSupportSeparatedSource S.coarse root target)
      (Receiver S root) :=
  { sources :=
      slabObservablePairedSupportSeparatedSources S.coarse root target
    sourceWeight := fun source =>
      slabObservableTwoReplicaPairWeight S.coarse source.1
    sourceCoefficient := fun source =>
      positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target source.1
    rowMass := fun _ => 1
    targets :=
      slabObservablePairedSupportDisconnectedFourCellTargetPairs
        S.coarse root target
    targets_nodup :=
      (slabObservableFourCellTargetPairs_nodup
        S.coarse root target).filter _
    targetWeight := slabObservableTwoReplicaPairWeight S.coarse
    targetCoefficient :=
      positiveExpandedFourCellTargetReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target
    Choice := SlabObservablePairedSupportRecouplingChoice
      S.coarse root target
    choices := slabObservablePairedSupportRecouplingChoices
      S.coarse root target
    localWeight := slabObservablePairedSupportRecouplingWeight
      S.coarse root target htarget
    realize := slabObservablePairedSupportRecoupledTargetPair
      S.coarse root target htarget
    coverage := fun source _ choice _ => by
      apply List.mem_filter.mpr
      exact
        ⟨slabObservablePairedSupportRecoupledTargetPair_mem
            S.coarse root target htarget source choice,
          by rw [slabObservablePairedSupportRecoupledTargetPair_disconnected]
             rfl⟩
    row_mass := fun source _ =>
      slabObservablePairedSupportRecouplingWeight_row_normalized
        S.coarse root target htarget source }

/-! ## 2. The explicit connected coefficient transport -/

/-- The first-source-thinned connected switch, restricted to its exact
connected target sector. -/
def actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    FiniteDependentCoefficientTransport
      (SlabObservablePairedConnectedStrandSource S.coarse root target)
      (Receiver S root) :=
  { sources := slabObservablePairedConnectedStrandSources
      S.coarse root target
    sourceWeight := fun source =>
      slabObservableTwoReplicaPairWeight S.coarse source.1
    sourceCoefficient := fun source =>
      positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target source.1
    rowMass := slabObservablePairedConnectedStrandThinnedRowMass
      S.coarse root target htarget
    targets := slabObservablePairedSupportConnectedFourCellTargetPairs
      S.coarse root target
    targets_nodup :=
      (slabObservableFourCellTargetPairs_nodup
        S.coarse root target).filter _
    targetWeight := slabObservableTwoReplicaPairWeight S.coarse
    targetCoefficient :=
      positiveExpandedFourCellTargetReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target
    Choice := SlabObservablePairedConnectedStrandChoice
      S.coarse root target
    choices := slabObservablePairedConnectedStrandChoices
      S.coarse root target
    localWeight := slabObservablePairedConnectedStrandThinnedWeight
      S.coarse root target htarget
    realize := slabObservablePairedConnectedStrandRealize
      S.coarse root target htarget
    coverage := fun source _ choice _ => by
      apply List.mem_filter.mpr
      exact
        ⟨slabObservablePairedConnectedStrandRealize_mem
            S.coarse root target htarget source choice,
          slabObservablePairedConnectedStrandRealize_connected
            S.coarse root target htarget source choice⟩
    row_mass := fun _ _ => Q'.eqv_refl _ }

/-! ## 3. Branch debts -/

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).rowCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).edgeCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).columnCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).rowCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).edgeCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).columnCoefficientDefect

/-- Exact normalization of the disconnected row kills its coefficient debt. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt_eqv_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt
        S hfineCutoff hcoarseCoupling root target htarget ≈ 0 := by
  let transport :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        transport.sourceWeight source *
          (transport.sourceCoefficient source *
            ((1 : Q') + -transport.rowMass source)))
      transport.sources) _ ?_ ?_
  · exact transport.rowCoefficientDefect_eqv_unretained
  · apply listQSum_eqv_zero_of_pointwise_local
    intro source _
    have hone : ((1 : Q') + -(1 : Q')) ≈ 0 :=
      Q'.add_neg_self_eqv 1
    refine Q'.eqv_trans _
      (transport.sourceWeight source *
        (transport.sourceCoefficient source * 0)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (transport.sourceWeight source) _ _
        (Q'.mul_eqv_congr_left (transport.sourceCoefficient source) _ _
          (by simpa only [transport,
              actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport]
            using hone))
    · exact Q'.eqv_trans _
        (transport.sourceWeight source * 0) _
        (Q'.mul_eqv_congr_left (transport.sourceWeight source) _ _
          (Q'.mul_zero_eqv (transport.sourceCoefficient source)))
        (Q'.mul_zero_eqv (transport.sourceWeight source))

/-! ## 4. Exact source and target sector partitions -/

theorem connectedTransport_sourceCoefficientMass_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
        S hfineCutoff hcoarseCoupling root target htarget).sourceCoefficientMass ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.coarse root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun receiver =>
        slabObservableTwoReplicaPairWeight S.coarse receiver *
          positiveExpandedFourCellSourceReceiverFiberScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        S.coarse root target)) _ ?_ ?_
  · exact Q'.eqv_of_eq (by
      simpa only [FiniteDependentCoefficientTransport.sourceCoefficientMass,
        actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport,
        slabObservablePairedConnectedStrandSources] using
        (listQSum_attach
          (fun receiver =>
            slabObservableTwoReplicaPairWeight S.coarse receiver *
              positiveExpandedFourCellSourceReceiverFiberScaleDefect
                S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.coarse root target)))
  · apply listQSum_congr
    intro receiver
    exact Q'.mul_comm_eqv _ _

theorem disconnectedTransport_sourceCoefficientMass_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
        S hfineCutoff hcoarseCoupling root target htarget).sourceCoefficientMass ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          S.coarse root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun receiver =>
        slabObservableTwoReplicaPairWeight S.coarse receiver *
          positiveExpandedFourCellSourceReceiverFiberScaleDefect
            S hfineCutoff hcoarseCoupling root target receiver)
      (slabObservablePairedSupportSeparatedFourCellSourcePairs
        S.coarse root target)) _ ?_ ?_
  · exact Q'.eqv_of_eq (by
      simpa only [FiniteDependentCoefficientTransport.sourceCoefficientMass,
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport,
        slabObservablePairedSupportSeparatedSources] using
        (listQSum_attach
          (fun receiver =>
            slabObservableTwoReplicaPairWeight S.coarse receiver *
              positiveExpandedFourCellSourceReceiverFiberScaleDefect
                S hfineCutoff hcoarseCoupling root target receiver)
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            S.coarse root target)))
  · apply listQSum_congr
    intro receiver
    exact Q'.mul_comm_eqv _ _

theorem connectedTransport_targetCoefficientMass_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
        S hfineCutoff hcoarseCoupling root target htarget).targetCoefficientMass ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservablePairedSupportConnectedFourCellTargetPairs
          S.coarse root target) := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    FiniteDependentCoefficientTransport.targetCoefficientMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_comm_eqv _ _

theorem disconnectedTransport_targetCoefficientMass_eqv
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
        S hfineCutoff hcoarseCoupling root target htarget).targetCoefficientMass ≈
      listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetReceiverFiberScaleDefect
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservablePairedSupportDisconnectedFourCellTargetPairs
          S.coarse root target) := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    FiniteDependentCoefficientTransport.targetCoefficientMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_comm_eqv _ _

/-! ## 5. The posterior-free five-debt identity -/

/-- Exact source/target sector partition followed by the two explicit
coefficient transports.  The disconnected row debt has already been deleted
using exact normalization. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitFiveDebts
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      ((actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) +
      (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget +
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) := by
  let sourceTerm := fun receiver : Receiver S root =>
    positiveExpandedFourCellSourceReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver *
      slabObservableTwoReplicaPairWeight S.coarse receiver
  let targetTerm := fun receiver : Receiver S root =>
    positiveExpandedFourCellTargetReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling root target receiver *
      slabObservableTwoReplicaPairWeight S.coarse receiver
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling root target htarget
  have hsourcePartition := listQSum_filter_partition sourceTerm
    (fun receiver => slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver)
    (slabObservableFourCellSourcePairs S.coarse root target)
  have htargetPartition := listQSum_filter_partition targetTerm
    (fun receiver => slabObservableTwoReplicaPairPairedSupportConnectedB
      S.coarse root target receiver)
    (slabObservableFourCellTargetPairs S.coarse root target)
  have hsource :
      positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
          S hfineCutoff hcoarseCoupling root target ≈
        connected.sourceCoefficientMass +
          disconnected.sourceCoefficientMass := by
    unfold positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
    refine Q'.eqv_trans _
      (listQSum sourceTerm
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.coarse root target) +
        listQSum sourceTerm
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            S.coarse root target)) _ ?_ ?_
    · simpa only [sourceTerm,
        slabObservablePairedSupportConnectedFourCellSourcePairs,
        slabObservablePairedSupportSeparatedFourCellSourcePairs] using
        hsourcePartition
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm
          (connectedTransport_sourceCoefficientMass_eqv
            S hfineCutoff hcoarseCoupling root target htarget))
        (Q'.eqv_symm
          (disconnectedTransport_sourceCoefficientMass_eqv
            S hfineCutoff hcoarseCoupling root target htarget))
  have htargetMass :
      positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
          S hfineCutoff hcoarseCoupling root target ≈
        connected.targetCoefficientMass +
          disconnected.targetCoefficientMass := by
    unfold positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
    refine Q'.eqv_trans _
      (listQSum targetTerm
          (slabObservablePairedSupportConnectedFourCellTargetPairs
            S.coarse root target) +
        listQSum targetTerm
          (slabObservablePairedSupportDisconnectedFourCellTargetPairs
            S.coarse root target)) _ ?_ ?_
    · simpa only [targetTerm,
        slabObservablePairedSupportConnectedFourCellTargetPairs,
        slabObservablePairedSupportDisconnectedFourCellTargetPairs] using
        htargetPartition
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm
          (connectedTransport_targetCoefficientMass_eqv
            S hfineCutoff hcoarseCoupling root target htarget))
        (Q'.eqv_symm
          (disconnectedTransport_targetCoefficientMass_eqv
            S hfineCutoff hcoarseCoupling root target htarget))
  have hbranches :
      actualPositiveExpandedReceiverFiberScaleDefectCross
          S hfineCutoff hcoarseCoupling root target ≈
        (connected.sourceCoefficientMass - connected.targetCoefficientMass) +
          (disconnected.sourceCoefficientMass -
            disconnected.targetCoefficientMass) := by
    unfold actualPositiveExpandedReceiverFiberScaleDefectCross
    refine Q'.eqv_trans _
      ((connected.sourceCoefficientMass + disconnected.sourceCoefficientMass) -
        (connected.targetCoefficientMass +
          disconnected.targetCoefficientMass)) _ ?_ ?_
    · exact sub_eqv_both_local hsource htargetMass
    · exact split_cross_local _ _ _ _
  have hconnected := connected.coefficientCross_eqv_row_add_edge_add_column
  have hdisconnected :=
    disconnected.coefficientCross_eqv_row_add_edge_add_column
  have hzero :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt_eqv_zero
      S hfineCutoff hcoarseCoupling root target htarget
  have hconnected' :
      connected.sourceCoefficientMass - connected.targetCoefficientMass ≈
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
            S hfineCutoff hcoarseCoupling root target htarget := by
    simpa only [connected,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt] using
      hconnected
  have hdisconnected' :
      disconnected.sourceCoefficientMass - disconnected.targetCoefficientMass ≈
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
            S hfineCutoff hcoarseCoupling root target htarget := by
    simpa only [disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt] using
      hdisconnected
  refine Q'.eqv_trans _
    (((actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget) +
      ((actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt
            S hfineCutoff hcoarseCoupling root target htarget +
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
            S hfineCutoff hcoarseCoupling root target htarget) +
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
          S hfineCutoff hcoarseCoupling root target htarget)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _ hbranches
      (Q'.add_eqv_congr' hconnected' hdisconnected')
  refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    ((0 +
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
          S hfineCutoff hcoarseCoupling root target htarget) +
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
        S hfineCutoff hcoarseCoupling root target htarget) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ hzero)
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_of_eq (Q'.zero_add'
        (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
          S hfineCutoff hcoarseCoupling root target htarget)))

/-! ## 6. Schedule-level five-debt producer -/

namespace PhysicalObservableRefinementSchedule

/-- Posterior-free schedule input for the two explicit split-sector kernels.
The five analytic fields are precisely the debts left after exact
disconnected-row normalization. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedRowCeiling : Q'
  connectedRowCeiling_pos : (0 : Q') < connectedRowCeiling
  connectedEdgeCeiling : Q'
  connectedEdgeCeiling_pos : (0 : Q') < connectedEdgeCeiling
  connectedColumnCeiling : Q'
  connectedColumnCeiling_pos : (0 : Q') < connectedColumnCeiling
  disconnectedEdgeCeiling : Q'
  disconnectedEdgeCeiling_pos : (0 : Q') < disconnectedEdgeCeiling
  disconnectedColumnCeiling : Q'
  disconnectedColumnCeiling_pos : (0 : Q') < disconnectedColumnCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedRowDebt_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem) ≤
      (connectedRowCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  connectedEdgeDebt_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem) ≤
      (connectedEdgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  connectedColumnDebt_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem) ≤
      (connectedColumnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  disconnectedEdgeDebt_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem) ≤
      (disconnectedEdgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  disconnectedColumnDebt_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem) ≤
      (disconnectedColumnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

def connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule) : Q' :=
  ((tail.connectedRowCeiling + tail.connectedEdgeCeiling) +
      tail.connectedColumnCeiling) +
    (tail.disconnectedEdgeCeiling + tail.disconnectedColumnCeiling)

theorem connectedCeiling_pos
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule) :
    (0 : Q') < tail.connectedCeiling := by
  unfold connectedCeiling
  exact Q'.add_pos
    (Q'.add_pos
      (Q'.add_pos
        tail.connectedRowCeiling_pos tail.connectedEdgeCeiling_pos)
      tail.connectedColumnCeiling_pos)
    (Q'.add_pos
      tail.disconnectedEdgeCeiling_pos tail.disconnectedColumnCeiling_pos)

/-- The exact five-debt identity commutes with the physical partition
normalization used by the covariance receiver. -/
theorem scaledCross_eqv_splitFiveDebts
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule)
    (scale : Nat) (_hscale : tail.start ≤ scale) :
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    factor *
        actualPositiveExpandedReceiverFiberScaleDefectCross
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget ≈
      (((factor *
              actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem +
            factor *
              actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem) +
          factor *
            actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem) +
        (factor *
              actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem +
          factor *
            actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem)) := by
  dsimp only
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let connectedRow :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  have hsplit :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitFiveDebts
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  refine Q'.eqv_trans _
    (factor *
      (((connectedRow + connectedEdge) + connectedColumn) +
        (disconnectedEdge + disconnectedColumn))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left factor _ _ (by
      simpa only [connectedRow, connectedEdge, connectedColumn,
        disconnectedEdge, disconnectedColumn] using hsplit)
  · refine Q'.eqv_trans _
      (factor * ((connectedRow + connectedEdge) + connectedColumn) +
        factor * (disconnectedEdge + disconnectedColumn)) _
      (Q'.mul_add_eqv factor
        ((connectedRow + connectedEdge) + connectedColumn)
        (disconnectedEdge + disconnectedColumn)) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _
        (factor * (connectedRow + connectedEdge) +
          factor * connectedColumn) _
        (Q'.mul_add_eqv factor (connectedRow + connectedEdge)
          connectedColumn)
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_add_eqv factor connectedRow connectedEdge)))
      (Q'.mul_add_eqv factor disconnectedEdge disconnectedColumn)

/-- The five schedule estimates combine without an extra majorization
constant. -/
theorem scaledCross_abs_le_connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectCross
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget) ≤
      (tail.connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale) := by
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let connectedRow :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  have htriangle :
      Q'.abs
          (factor *
            actualPositiveExpandedReceiverFiberScaleDefectCross
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget) ≤
        ((Q'.abs (factor * connectedRow) +
            Q'.abs (factor * connectedEdge)) +
          Q'.abs (factor * connectedColumn)) +
        (Q'.abs (factor * disconnectedEdge) +
          Q'.abs (factor * disconnectedColumn)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (tail.scaledCross_eqv_splitFiveDebts scale hscale))) ?_
    exact Q'.le_trans' _ _ _
      (Q'.abs_add_le'
        ((factor * connectedRow + factor * connectedEdge) +
          factor * connectedColumn)
        (factor * disconnectedEdge + factor * disconnectedColumn))
      (Q'.add_le_add
        (Q'.le_trans' _ _ _
          (Q'.abs_add_le'
            (factor * connectedRow + factor * connectedEdge)
            (factor * connectedColumn))
          (Q'.add_le_add
            (Q'.abs_add_le'
              (factor * connectedRow) (factor * connectedEdge))
            (Q'.le_refl' (Q'.abs (factor * connectedColumn)))))
        (Q'.abs_add_le'
          (factor * disconnectedEdge) (factor * disconnectedColumn)))
  have hdebts :
      ((Q'.abs (factor * connectedRow) +
          Q'.abs (factor * connectedEdge)) +
        Q'.abs (factor * connectedColumn)) +
        (Q'.abs (factor * disconnectedEdge) +
          Q'.abs (factor * disconnectedColumn)) ≤
      (((tail.connectedRowCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) +
          (tail.connectedEdgeCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale)) +
        (tail.connectedColumnCeiling * schedule.spacing.spacing scale) *
          connectedCovarianceRawCrossDenominator (schedule.scalePair scale)) +
        ((tail.disconnectedEdgeCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) +
          (tail.disconnectedColumnCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator
              (schedule.scalePair scale)) := by
    exact Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add
          (by simpa only [factor, connectedRow] using
            tail.connectedRowDebt_le scale hscale)
          (by simpa only [factor, connectedEdge] using
            tail.connectedEdgeDebt_le scale hscale))
        (by simpa only [factor, connectedColumn] using
          tail.connectedColumnDebt_le scale hscale))
      (Q'.add_le_add
        (by simpa only [factor, disconnectedEdge] using
          tail.disconnectedEdgeDebt_le scale hscale)
        (by simpa only [factor, disconnectedColumn] using
          tail.disconnectedColumnDebt_le scale hscale))
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ hdebts
      (Q'.le_of_eqv
        (add_five_scaled_local
          tail.connectedRowCeiling tail.connectedEdgeCeiling
          tail.connectedColumnCeiling tail.disconnectedEdgeCeiling
          tail.disconnectedColumnCeiling
          (schedule.spacing.spacing scale)
          (connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)))))

/-- Compile the two explicit kernels and their five analytic debts into the
existing one-cross receiver. -/
def toScaleDefectSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectSeparatedLinearRawTransportTail
      schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  actualPositiveExpandedReceiverFiberScaleDefect_le :=
    fun scale hscale => tail.scaledCross_abs_le_connectedCeiling scale hscale

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toScaleDefectSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        (((tail.connectedRowCeiling + tail.connectedEdgeCeiling) +
            tail.connectedColumnCeiling) +
          (tail.disconnectedEdgeCeiling +
            tail.disconnectedColumnCeiling)) :=
  rfl

/-- Final matched covariance consumer for the explicit split-sector route. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedRowDebt_eqv_zero
#print axioms connectedTransport_sourceCoefficientMass_eqv
#print axioms disconnectedTransport_sourceCoefficientMass_eqv
#print axioms connectedTransport_targetCoefficientMass_eqv
#print axioms disconnectedTransport_targetCoefficientMass_eqv
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitFiveDebts
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.connectedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.scaledCross_eqv_splitFiveDebts
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.scaledCross_abs_le_connectedCeiling
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitFiveDebtLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
