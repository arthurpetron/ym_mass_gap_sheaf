/-
# A positive-density good-source congestion route to the face gap

Some support-connected strand rows can have no successful disconnection
channel.  Requiring one selected channel in every connected row is therefore
stronger than the aggregate observable argument needs.  This module selects
an explicit Boolean subcarrier of good connected sources instead.

Three quantitative inputs suffice:

* the good sources carry at least a fraction `rho` of the complete connected
  physical source mass;
* every good source has one successful channel of weight at least `eta`;
* every selected target has at most `congestion + 1` good-source preimages.

The selected-channel congestion compiler transports at least

```text
  rho * eta / (congestion + 1)
```

of the complete connected sector.  Gluing it to the disconnected switch and
then applying the variance bridge gives the genuine reflected same-object
relative face-form gap.  Bad connected rows may have zero successful mass.

No good-source density, choice family, or congestion bound is inhabited here.
Constructive contract: executable source filtering, attached dependent
carriers, exact finite weighted sums, and the physical SU(2) realization only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableSelectedChoiceCongestionContraction
import YMGap.Continuum.FiniteWeightedGoodSourceRepair

namespace YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction

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
open YMGap.Continuum.CompactDualSlabObservableSelectedChoiceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion.SelectedChoiceCongestionCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGoodSourceRepair
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance goodSourceCongestionPairDecidableEq
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

/-! ## 1. Executable good connected sources -/

def slabObservablePairedConnectedGoodSources
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    List (SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :=
  (slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId).filter goodB

abbrev SlabObservablePairedConnectedGoodSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :=
  {source // source ∈ slabObservablePairedConnectedGoodSources
    D rootFaceId targetFaceId goodB}

def slabObservablePairedConnectedGoodSourceList
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    List (SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :=
  (slabObservablePairedConnectedGoodSources
    D rootFaceId targetFaceId goodB).attach

def slabObservablePairedConnectedGoodSourceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) : Q' :=
  listQSum
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairedConnectedGoodSources
      D rootFaceId targetFaceId goodB)

/-- Filtering the nonnegative connected physical source mass by any
executable good predicate can only decrease it. -/
theorem slabObservablePairedConnectedGoodSourceMass_le_sourceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB ≤
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId := by
  unfold slabObservablePairedConnectedGoodSourceMass
    slabObservablePairedConnectedGoodSources
    slabObservablePairedConnectedStrandSources
    slabObservablePairedConnectedSourceMass
  exact listQSum_filter_attach_le
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (fun pair _ => slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId pair)
    goodB

def SlabObservablePairedConnectedGoodSource.toChoiceSource
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :
    SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId :=
  source.1

/-! ## 2. Independent density and routing witnesses -/

/-- A positive fraction of the complete connected physical mass lies on an
executable Boolean subcarrier. -/
structure SlabObservablePairedConnectedGoodSourceDensity
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool)
    (rho : Q') : Type where
  rho_pos : (0 : Q') < rho
  rho_le_one : rho ≤ (1 : Q')
  good_mass_floor :
    rho * slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId ≤
      slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB

/-- One successful selected channel in every good source, with a common local
weight floor and a bound on selected target multiplicity. -/
structure SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool)
    (eta : Q') (congestion : Nat) : Type where
  eta_pos : (0 : Q') < eta
  eta_le_one : eta ≤ (1 : Q')
  choice : ∀ source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB,
    SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source.toChoiceSource
  choice_mem : ∀ source,
    choice source ∈ slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source.toChoiceSource
  choice_weight_floor : ∀ source,
    eta ≤ slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId source.toChoiceSource (choice source)
  fiber_count_le : ∀ target,
    (selectedTargetFiber
      (slabObservablePairedConnectedGoodSourceList
        D rootFaceId targetFaceId goodB)
      (fun source : SlabObservablePairedConnectedGoodSource
        D rootFaceId targetFaceId goodB =>
          SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId source.toChoiceSource)
      choice
      (fun source => slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget source.toChoiceSource)
      target).length ≤ congestion + 1

namespace SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion

/-- The physical good-source routing witness specializes the generic finite
selected-choice congestion certificate. -/
def toFiniteCertificate
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    SelectedChoiceCongestionCertificate
      (slabObservablePairedConnectedGoodSourceList
        D rootFaceId targetFaceId goodB)
      (fun source : SlabObservablePairedConnectedGoodSource
        D rootFaceId targetFaceId goodB =>
          SlabObservablePairedConnectedStrandChoice
            D rootFaceId targetFaceId source.toChoiceSource)
      (fun source => slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId source.toChoiceSource)
      (fun source => slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId source.toChoiceSource)
      (fun source => slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget source.toChoiceSource)
      eta congestion where
  eta_pos := routing.eta_pos
  eta_le_one := routing.eta_le_one
  selected := routing.choice
  selected_mem := fun source _ => routing.choice_mem source
  selected_weight_nonnegative := fun source _ =>
    slabObservablePairedConnectedStrandWeight_nonnegative
      D rootFaceId targetFaceId source.toChoiceSource (routing.choice source)
  selected_weight_floor := fun source _ => routing.choice_weight_floor source
  selected_weight_le_one := by
    intro source _
    exact Q'.le_trans' _ _ _
      (listQSum_member_le_nonnegative_local
        (slabObservablePairedConnectedStrandWeight
          D rootFaceId targetFaceId source.toChoiceSource)
        (slabObservablePairedConnectedStrandWeight_nonnegative
          D rootFaceId targetFaceId source.toChoiceSource)
        (slabObservablePairedConnectedStrandChoices
          D rootFaceId targetFaceId source.toChoiceSource)
        (routing.choice_mem source))
      (slabObservablePairedConnectedStrandWeight_row_le_one
        D rootFaceId targetFaceId source.toChoiceSource)
  fiber_count_le := routing.fiber_count_le

/-- The total retained fraction of the full connected source sector. -/
def fraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion)
    (rho : Q') : Q' :=
  routing.toFiniteCertificate.fraction * rho

theorem fraction_pos
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho eta : Q'} {congestion : Nat}
    (density : SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    (0 : Q') < routing.fraction rho :=
  Q'.mul_pos routing.toFiniteCertificate.fraction_pos density.rho_pos

theorem fraction_le_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho eta : Q'} {congestion : Nat}
    (density : SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    routing.fraction rho ≤ (1 : Q') := by
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    routing.toFiniteCertificate.fraction 1 rho
    routing.toFiniteCertificate.fraction_le_one (Q'.le_of_lt density.rho_pos)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv rho)) density.rho_le_one)

def selectedRowMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion)
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) : Q' :=
  let finite := routing.toFiniteCertificate
  listQSum (finite.scaledLocalWeight source) (scaledChoices source)

def selectedTransportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) : Q' :=
  listQSum
    (fun source =>
      slabObservableTwoReplicaPairWeight D source.1.1 *
        routing.selectedRowMass source)
    (slabObservablePairedConnectedGoodSourceList
      D rootFaceId targetFaceId goodB)

theorem finiteFraction_le_selectedRowMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion)
    (source : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB) :
    routing.toFiniteCertificate.fraction ≤ routing.selectedRowMass source := by
  unfold selectedRowMass
  exact routing.toFiniteCertificate.fraction_le_scaledRowMass source
    (List.mem_attach _ source)

/-! ## 3. Selected good-source transport -/

theorem selectedWeightedColumn_le
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    let finite := routing.toFiniteCertificate
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1.1 *
          dependentKernelPushforwardWeight
            (fun _ : SlabObservablePairedConnectedGoodSource
              D rootFaceId targetFaceId goodB => Unit)
            scaledChoices finite.scaledLocalWeight finite.scaledRealize
            source target)
        (slabObservablePairedConnectedGoodSourceList
          D rootFaceId targetFaceId goodB) ≤
      slabObservableTwoReplicaPairWeight D target := by
  dsimp only
  let finite := routing.toFiniteCertificate
  apply weightedColumn_le_of_columnCapacity
    (slabObservablePairedConnectedGoodSourceList
      D rootFaceId targetFaceId goodB)
    (fun source => slabObservableTwoReplicaPairWeight D source.1.1)
    (slabObservableTwoReplicaPairWeight D)
    (fun _ : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB => Unit)
    scaledChoices finite.scaledLocalWeight finite.scaledRealize target
  · exact slabObservableTwoReplicaPairWeight_nonnegative D rootFaceId target
  · intro source _ choice heq
    subst target
    cases choice
    exact Q'.eqv_symm
      (slabObservablePairedStrandRecoupledTargetPair_weight_preserved
        D rootFaceId targetFaceId htarget
        source.toChoiceSource.toRecouplingSource (routing.choice source))
  · exact finite.scaledColumn_le_one target

theorem selectedTransportedMass_le_connectedTarget
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    routing.selectedTransportedMass ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  let finite := routing.toFiniteCertificate
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    (slabObservablePairedConnectedGoodSourceList
      D rootFaceId targetFaceId goodB)
    (fun source => slabObservableTwoReplicaPairWeight D source.1.1)
    routing.selectedRowMass
    (slabObservablePairedSupportConnectedFourCellTargetPairs
      D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (fun _ : SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB => Unit)
    scaledChoices finite.scaledLocalWeight finite.scaledRealize
    ((slabObservableFourCellTargetPairs_nodup
      D rootFaceId targetFaceId).filter _)
    (fun source _ choice _ => by
      cases choice
      apply List.mem_filter.mpr
      exact ⟨slabObservablePairedConnectedStrandRealize_mem
          D rootFaceId targetFaceId htarget source.toChoiceSource
            (routing.choice source),
        slabObservablePairedConnectedStrandRealize_connected
          D rootFaceId targetFaceId htarget source.toChoiceSource
            (routing.choice source)⟩)
    (fun _ _ => Q'.eqv_refl _)
    (fun target _ => routing.selectedWeightedColumn_le target)

/-! ## 4. Positive good-source density gives the aggregate fraction -/

theorem finiteFraction_mul_goodMass_le_selectedTransportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {eta : Q'} {congestion : Nat}
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    routing.toFiniteCertificate.fraction *
        slabObservablePairedConnectedGoodSourceMass
          D rootFaceId targetFaceId goodB ≤
      routing.selectedTransportedMass := by
  let sources := slabObservablePairedConnectedGoodSourceList
    D rootFaceId targetFaceId goodB
  let sourceWeight := fun source :
      SlabObservablePairedConnectedGoodSource
        D rootFaceId targetFaceId goodB =>
    slabObservableTwoReplicaPairWeight D source.1.1
  have hsource : listQSum sourceWeight sources ≈
      slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB := by
    apply Q'.eqv_of_eq
    unfold sources sourceWeight
      slabObservablePairedConnectedGoodSourceList
      slabObservablePairedConnectedGoodSourceMass
    exact listQSum_attach
      (fun source : SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId =>
          slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedConnectedGoodSources
        D rootFaceId targetFaceId goodB)
  have hleft :
      routing.toFiniteCertificate.fraction *
          slabObservablePairedConnectedGoodSourceMass
            D rootFaceId targetFaceId goodB ≈
        listQSum
          (fun source => routing.toFiniteCertificate.fraction *
            sourceWeight source) sources := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left routing.toFiniteCertificate.fraction _ _
        (Q'.eqv_symm hsource))
      (Q'.eqv_symm
        (listQSum_mul_left routing.toFiniteCertificate.fraction
          sourceWeight sources))
  have hterms :
      listQSum
          (fun source => routing.toFiniteCertificate.fraction *
            sourceWeight source) sources ≤
        listQSum
          (fun source => sourceWeight source * routing.selectedRowMass source)
          sources := by
    apply listQSum_le_termwise_local
    intro source _
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      routing.toFiniteCertificate.fraction (routing.selectedRowMass source)
      (sourceWeight source)
      (routing.finiteFraction_le_selectedRowMass source)
      (slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1.1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv routing.toFiniteCertificate.fraction
          (sourceWeight source)))
      hscaled
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hterms

theorem fraction_mul_sourceMass_le_selectedTransportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho eta : Q'} {congestion : Nat}
    (density : SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    routing.fraction rho * slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId ≤
      routing.selectedTransportedMass := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (rho * slabObservablePairedConnectedSourceMass
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedGoodSourceMass
      D rootFaceId targetFaceId goodB)
    routing.toFiniteCertificate.fraction density.good_mass_floor
    (Q'.le_of_lt routing.toFiniteCertificate.fraction_pos)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_assoc_eqv routing.toFiniteCertificate.fraction rho
        (slabObservablePairedConnectedSourceMass
          D rootFaceId targetFaceId)))
    (Q'.le_trans' _ _ _ hscaled
      routing.finiteFraction_mul_goodMass_le_selectedTransportedMass)

/-! ## 5. Retained contraction and reflected relative form gap -/

def toRetainedContraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho eta : Q'} {congestion : Nat}
    (density : SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta congestion) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId where
  fraction := routing.fraction rho
  fraction_pos := fraction_pos density routing
  fraction_le_one := fraction_le_one density routing
  disconnected_add_fraction_mul_connected_le_target := by
    have hbranches := Q'.add_le_add
      (slabObservablePairedSupportSeparated_weight_le_disconnectedTarget
        D rootFaceId targetFaceId htarget)
      routing.selectedTransportedMass_le_connectedTarget
    have hfloor := Q'.add_le_add
      (Q'.le_refl'
        (listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            D rootFaceId targetFaceId)))
      (fraction_mul_sourceMass_le_selectedTransportedMass density routing)
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

theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    {goodB : SlabObservablePairedConnectedStrandSource D rootFaceId
      (slabFaceReflectId D.extent rootFaceId) → Bool}
    {rho eta : Q'} {congestion : Nat}
    (density : SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId (slabFaceReflectId D.extent rootFaceId) goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hroot).1)
      goodB eta congestion) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      ((1 : Q') + -routing.fraction rho) *
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
      D hroot (toRetainedContraction density routing)

#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.toFiniteCertificate
#print axioms slabObservablePairedConnectedGoodSourceMass_le_sourceMass
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.fraction_pos
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.fraction_le_one
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.selectedTransportedMass_le_connectedTarget
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.fraction_mul_sourceMass_le_selectedTransportedMass
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.toRetainedContraction
#print axioms SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion

end YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
