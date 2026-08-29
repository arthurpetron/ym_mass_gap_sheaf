/-
# Bounded selected-channel congestion gives a reflected face contraction

The first-source route requires every connected source to own a target which
no earlier row reaches.  A component peel is more naturally many-to-one.  We
therefore keep one successful SU(2) strand channel in every connected row and
divide its probability by a proved target-fiber congestion bound.

The generic selected-choice theorem supplies unit column capacity and the
common retained row fraction `invSucc congestion * eta`.  Exact physical
weight preservation upgrades that to weighted capacity.  Since selected
successful outputs remain in the connected target sector, it can be glued to
the already normalized disconnected switch without spending any target twice.
The result is the existing retained-contraction certificate and hence the
relative same-object centered face-form bound.

No source-wide selected family or congestion bound is inhabited here.  The
module changes the exact open input from a collision-free matching to a
bounded many-to-one map.  Constructive contract: explicit dependent choices,
finite fibers, exact `Q'`, and the physical SU(2) realization only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
import YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
import YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion

namespace YMGap.Continuum.CompactDualSlabObservableSelectedChoiceCongestionContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion.SelectedChoiceCongestionCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance selectedCongestionPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. The concrete SU(2) selected-channel input -/

/-- One successful channel in every connected source row, with a common
positive weight floor and a uniform bound on the number of selected sources
which realize the same physical target. -/
structure SlabObservablePairedConnectedSelectedChoiceCongestion
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (eta : Q') (congestion : Nat) : Type where
  eta_pos : (0 : Q') < eta
  eta_le_one : eta ≤ (1 : Q')
  choice : ∀ source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId,
    SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source
  choice_mem : ∀ source,
    choice source ∈ slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source
  choice_weight_floor : ∀ source,
    eta ≤ slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId source (choice source)
  fiber_count_le : ∀ target,
    (selectedTargetFiber
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      choice
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      target).length ≤ congestion + 1

namespace SlabObservablePairedConnectedSelectedChoiceCongestion

/-- The physical input specializes the generic finite selected-choice
congestion certificate. -/
def toFiniteCertificate
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion) :
    SelectedChoiceCongestionCertificate
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      eta congestion where
  eta_pos := data.eta_pos
  eta_le_one := data.eta_le_one
  selected := data.choice
  selected_mem := fun source _ => data.choice_mem source
  selected_weight_nonnegative := fun source _ =>
    slabObservablePairedConnectedStrandWeight_nonnegative
      D rootFaceId targetFaceId source (data.choice source)
  selected_weight_floor := fun source _ => data.choice_weight_floor source
  selected_weight_le_one := by
    intro source _
    exact Q'.le_trans' _ _ _
      (listQSum_member_le_nonnegative_local
        (slabObservablePairedConnectedStrandWeight
          D rootFaceId targetFaceId source)
        (slabObservablePairedConnectedStrandWeight_nonnegative
          D rootFaceId targetFaceId source)
        (slabObservablePairedConnectedStrandChoices
          D rootFaceId targetFaceId source)
        (data.choice_mem source))
      (slabObservablePairedConnectedStrandWeight_row_le_one
        D rootFaceId targetFaceId source)
  fiber_count_le := data.fiber_count_le

/-- The retained connected row mass of the scaled selected channel. -/
def selectedRowMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : Q' :=
  let finite := data.toFiniteCertificate
  listQSum (finite.scaledLocalWeight source) (scaledChoices source)

/-- Total physical connected mass transported by the scaled selected
channels. -/
def selectedTransportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion) : Q' :=
  listQSum
    (fun source => slabObservableTwoReplicaPairWeight D source.1 *
      data.selectedRowMass source)
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)

/-- Every selected connected row retains the same displayed fraction. -/
theorem fraction_le_selectedRowMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    data.toFiniteCertificate.fraction ≤ data.selectedRowMass source := by
  unfold selectedRowMass
  exact data.toFiniteCertificate.fraction_le_scaledRowMass source
    (List.mem_attach _ source)

/-! ## 2. Physical column capacity and the connected target budget -/

theorem selectedWeightedColumn_le
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    let finite := data.toFiniteCertificate
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1 *
          dependentKernelPushforwardWeight
            (fun _ : SlabObservablePairedConnectedStrandSource
              D rootFaceId targetFaceId => Unit)
            scaledChoices finite.scaledLocalWeight finite.scaledRealize
            source target)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≤
      slabObservableTwoReplicaPairWeight D target := by
  dsimp only
  let finite := data.toFiniteCertificate
  apply weightedColumn_le_of_columnCapacity
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservableTwoReplicaPairWeight D)
    (fun _ : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId => Unit)
    scaledChoices finite.scaledLocalWeight finite.scaledRealize target
  · exact slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId target
  · intro source _ choice heq
    subst target
    cases choice
    exact Q'.eqv_symm
      (slabObservablePairedStrandRecoupledTargetPair_weight_preserved
        D rootFaceId targetFaceId htarget
        source.toRecouplingSource (data.choice source))
  · exact finite.scaledColumn_le_one target

/-- The selected connected kernel spends only the support-connected target
sector. -/
theorem selectedTransportedMass_le_connectedTarget
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion) :
    data.selectedTransportedMass ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  let finite := data.toFiniteCertificate
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    data.selectedRowMass
    (slabObservablePairedSupportConnectedFourCellTargetPairs
      D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (fun _ : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId => Unit)
    scaledChoices finite.scaledLocalWeight finite.scaledRealize
    ((slabObservableFourCellTargetPairs_nodup
      D rootFaceId targetFaceId).filter _)
    (fun source _ choice _ => by
      cases choice
      apply List.mem_filter.mpr
      exact ⟨slabObservablePairedConnectedStrandRealize_mem
          D rootFaceId targetFaceId htarget source (data.choice source),
        slabObservablePairedConnectedStrandRealize_connected
          D rootFaceId targetFaceId htarget source (data.choice source)⟩)
    (fun _ _ => Q'.eqv_refl _)
    (fun target _ => data.selectedWeightedColumn_le target)

/-! ## 3. Aggregate fraction and retained contraction -/

/-- The common selected row fraction survives physical Gibbs weighting and
finite summation. -/
theorem fraction_mul_sourceMass_le_selectedTransportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion) :
    data.toFiniteCertificate.fraction *
        slabObservablePairedConnectedSourceMass
          D rootFaceId targetFaceId ≤
      data.selectedTransportedMass := by
  let sources := slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId
  let sourceWeight := fun source :
      SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId =>
    slabObservableTwoReplicaPairWeight D source.1
  have hsource : listQSum sourceWeight sources ≈
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId := by
    apply Q'.eqv_of_eq
    unfold sources sourceWeight
      slabObservablePairedConnectedStrandSources
      slabObservablePairedConnectedSourceMass
    exact listQSum_attach
      (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId)
  have hleft :
      data.toFiniteCertificate.fraction *
          slabObservablePairedConnectedSourceMass
            D rootFaceId targetFaceId ≈
        listQSum
          (fun source => data.toFiniteCertificate.fraction *
            sourceWeight source) sources := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left data.toFiniteCertificate.fraction _ _
        (Q'.eqv_symm hsource))
      (Q'.eqv_symm
        (listQSum_mul_left data.toFiniteCertificate.fraction
          sourceWeight sources))
  have hterms :
      listQSum
          (fun source => data.toFiniteCertificate.fraction *
            sourceWeight source) sources ≤
        listQSum
          (fun source => sourceWeight source * data.selectedRowMass source)
          sources := by
    apply listQSum_le_termwise_local
    intro source _
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      data.toFiniteCertificate.fraction (data.selectedRowMass source)
      (sourceWeight source)
      (data.fraction_le_selectedRowMass source)
      (slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv data.toFiniteCertificate.fraction
          (sourceWeight source)))
      hscaled
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hterms

/-- Gluing the full disconnected switch to the scaled selected connected
kernel yields the literal retained-contraction certificate. -/
def toRetainedContraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget eta congestion) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId where
  fraction := data.toFiniteCertificate.fraction
  fraction_pos := data.toFiniteCertificate.fraction_pos
  fraction_le_one := data.toFiniteCertificate.fraction_le_one
  disconnected_add_fraction_mul_connected_le_target := by
    have hbranches := Q'.add_le_add
      (slabObservablePairedSupportSeparated_weight_le_disconnectedTarget
        D rootFaceId targetFaceId htarget)
      data.selectedTransportedMass_le_connectedTarget
    have hfloor := Q'.add_le_add
      (Q'.le_refl'
        (listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            D rootFaceId targetFaceId)))
      data.fraction_mul_sourceMass_le_selectedTransportedMass
    have htargets :
        listQSum (slabObservableTwoReplicaPairWeight D)
            (slabObservablePairedSupportDisconnectedFourCellTargetPairs
              D rootFaceId targetFaceId) +
          listQSum (slabObservableTwoReplicaPairWeight D)
            (slabObservablePairedSupportConnectedFourCellTargetPairs
              D rootFaceId targetFaceId) ≈
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) :=
      Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv _ _)
        (Q'.eqv_symm
          (slabObservableFourCellTargetPairs_pairedSupport_partition
            D rootFaceId targetFaceId))
    exact Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _ hbranches (Q'.le_of_eqv htargets))

/-! ## 4. The genuine same-object relative face-form conclusion -/

theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    {eta : Q'} {congestion : Nat}
    (data : SlabObservablePairedConnectedSelectedChoiceCongestion
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      (slabFaceReflectId_physical
        (mem_centralLowerFaceIds.mp hroot).1)
      eta congestion) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      ((1 : Q') + -data.toFiniteCertificate.fraction) *
        centralPhysicalWeightedInner
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value) := by
  exact
    CompactDualSlabObservableFaceVarianceBridge.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
      D hroot data.toRetainedContraction

#print axioms SlabObservablePairedConnectedSelectedChoiceCongestion.toFiniteCertificate
#print axioms SlabObservablePairedConnectedSelectedChoiceCongestion.selectedTransportedMass_le_connectedTarget
#print axioms SlabObservablePairedConnectedSelectedChoiceCongestion.fraction_mul_sourceMass_le_selectedTransportedMass
#print axioms SlabObservablePairedConnectedSelectedChoiceCongestion.toRetainedContraction
#print axioms SlabObservablePairedConnectedSelectedChoiceCongestion.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end SlabObservablePairedConnectedSelectedChoiceCongestion

end YMGap.Continuum.CompactDualSlabObservableSelectedChoiceCongestionContraction
