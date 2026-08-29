/-
# Canonical terminal packing compiles to weighted good-source repair

The canonical peeling estimate is strongest when its variable reconstruction
payments are retained inside each receiver fiber.  This module performs that
contraction.

First, the terminal-fiber estimate is transported from proof-carrying
four-cell entries to the literal connected strand-source carrier.  Then an
injective terminal packing is used as the repair map:

```text
  connected source -> canonical terminal -> packed good source.
```

Injectivity of the packing makes every repair fiber lie in one canonical
terminal fiber.  The geometric peeling estimate bounds that fiber by
`globalAnchorRate * terminalWeight`; the packing's insertion floor converts
the terminal weight into the actual good-target weight.  Hence any `rho`
satisfying

```text
  rho * globalAnchorRate <= kappa
```

gives the weighted inverse-fiber capacity required by the physical repair
compiler.  No pointwise minimum and no unweighted source congestion appears.

Constructive contract: finite attached carriers, injective maps, exact
rational order, and the proved terminal-fiber estimate only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingTerminalFiber
import YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourcePacking
import YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourcePacking
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingTerminalFiber
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance canonicalFiberRepairPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

/-! ## 1. The literal connected-source terminal map -/

/-- Canonical target-support terminal of a connected strand source. -/
def slabObservablePairedConnectedCanonicalTerminal
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) : SlabAcceptedTwoReplicaState D :=
  slabObservablePairTargetSupportCanonicalPeelingTerminal
    D rootFaceId targetFaceId htarget source.toRecouplingSource

/-- The connected source's proof-carrying four-cell presentation. -/
def slabObservablePairedConnectedSourceEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    SlabObservableFourCellPairEntry D rootFaceId targetFaceId :=
  ⟨source.1, (List.mem_filter.mp source.2).1⟩

theorem slabObservablePairedConnectedSourceEntry_mem_connectedEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    slabObservablePairedConnectedSourceEntry
        D rootFaceId targetFaceId source ∈
      slabObservablePairedSupportConnectedFourCellSourceEntries
        D rootFaceId targetFaceId := by
  unfold slabObservablePairedConnectedSourceEntry
    slabObservablePairedSupportConnectedFourCellSourceEntries
  apply List.mem_filter.mpr
  exact ⟨List.mem_attach _ source.toRecouplingSource,
    source.connected⟩

theorem slabObservablePairedConnectedSourceEntry_injective
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (left right : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (heq : slabObservablePairedConnectedSourceEntry
        D rootFaceId targetFaceId left =
      slabObservablePairedConnectedSourceEntry
        D rootFaceId targetFaceId right) :
    left = right := by
  cases left with
  | mk left hleft =>
      cases right with
      | mk right hright =>
          apply Subtype.ext
          change left = right
          change (⟨left, _⟩ : SlabObservableFourCellPairEntry
              D rootFaceId targetFaceId) = ⟨right, _⟩ at heq
          exact Subtype.ext_iff.mp heq

/-! ## 2. Transport the terminal-fiber estimate to strand sources -/

/-- The same terminal-fiber estimate on the exact carrier consumed by the
good-source repair interface. -/
theorem slabObservablePairedConnectedCanonicalTerminal_fiberWeight_le
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) :
    let D := anchorSlabPhysicalData cutoff half
    fiberWeight
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairedConnectedCanonicalTerminal
          D rootFaceId targetFaceId htarget)
        terminal ≤
      slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let D := anchorSlabPhysicalData cutoff half
  let sourceCarrier := slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId
  let entryCarrier :=
    slabObservablePairedSupportConnectedFourCellSourceEntries
      D rootFaceId targetFaceId
  let sourceTerminal := slabObservablePairedConnectedCanonicalTerminal
    D rootFaceId targetFaceId htarget
  let entryTerminal :=
    slabObservablePairTargetSupportCanonicalPeelingTerminal
      D rootFaceId targetFaceId htarget
  let sourceFiber := sourceCarrier.filter
    (fun source => decide (terminal = sourceTerminal source))
  let entryFiber := entryCarrier.filter
    (fun source => decide (terminal = entryTerminal source))
  have hinjection :
      listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          sourceFiber ≤
        listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          entryFiber := by
    apply listQSum_le_of_injective
      sourceFiber entryFiber
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedConnectedSourceEntry
        D rootFaceId targetFaceId)
    · exact List.filter_sublist.nodup
        (slabObservablePairedConnectedStrandSources_nodup
          D rootFaceId targetFaceId)
    · intro source hsource
      apply List.mem_filter.mpr
      refine ⟨slabObservablePairedConnectedSourceEntry_mem_connectedEntries
        D rootFaceId targetFaceId source, ?_⟩
      have hterminal := (List.mem_filter.mp hsource).2
      exact hterminal
    · intro left _ right _ heq
      exact slabObservablePairedConnectedSourceEntry_injective
        D rootFaceId targetFaceId left right heq
    · intro source _
      exact Q'.le_refl' _
    · intro source _
      exact slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1
  change listQSum
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      sourceFiber ≤ _
  exact Q'.le_trans' _ _ _ hinjection
    (slabObservablePairedSupportCanonicalPeeling_terminalFiberWeight_le
      cutoff half rootFaceId targetFaceId htarget terminal)

/-! ## 3. Injective terminal packing is a weighted repair -/

/-- Repair a connected source by peeling it completely and packing its
deterministic terminal into the good subcarrier. -/
def slabObservablePairedConnectedCanonicalPackedRepair
    {cutoff half rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa : Q'}
    (data : SlabObservablePairedConnectedGoodTerminalPacking
      cutoff half rootFaceId targetFaceId goodB kappa)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (source : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId) :
    SlabObservablePairedConnectedGoodSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId goodB :=
  data.pack
    (slabObservablePairedConnectedCanonicalTerminal
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget source)

/-- **Weighted repair compiler.**  An injective terminal packing with
insertion floor `kappa` converts canonical peeling directly into the literal
weighted good-source fiber repair. -/
def SlabObservablePairedConnectedGoodTerminalPacking.toFiberRepair
    {cutoff half rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa rho : Q'}
    (data : SlabObservablePairedConnectedGoodTerminalPacking
      cutoff half rootFaceId targetFaceId goodB kappa)
    (rho_pos : (0 : Q') < rho)
    (rho_le_one : rho ≤ (1 : Q'))
    (rate_budget :
      rho * slabObservablePairedSupportGlobalAnchorRate
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId ≤ kappa) :
    SlabObservablePairedConnectedGoodSourceFiberRepair
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId goodB rho where
  rho_pos := rho_pos
  rho_le_one := rho_le_one
  repair := slabObservablePairedConnectedCanonicalPackedRepair data htarget
  weighted_fiber_capacity := by
    intro target
    let D := anchorSlabPhysicalData cutoff half
    let sources := slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId
    let terminalCode := slabObservablePairedConnectedCanonicalTerminal
      D rootFaceId targetFaceId htarget
    let repair := slabObservablePairedConnectedCanonicalPackedRepair
      data htarget
    cases hfiber : sources.filter
        (fun source => decide (target = repair source)) with
    | nil =>
        change rho * listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          (sources.filter
            (fun source => decide (target = repair source))) ≤ _
        rw [hfiber]
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_zero_eqv rho))
          (slabObservableTwoReplicaPairWeight_nonnegative
            D rootFaceId target.1.1)
    | cons first rest =>
        have hfirstMem : first ∈ sources.filter
            (fun source => decide (target = repair source)) := by
          rw [hfiber]
          exact List.mem_cons_self
        have hfirstEq : target = repair first :=
          of_decide_eq_true (List.mem_filter.mp hfirstMem).2
        have hfilter :
            listQSum
                (fun source => slabObservableTwoReplicaPairWeight D source.1)
                (sources.filter
                  (fun source => decide (target = repair source))) ≤
              listQSum
                (fun source => slabObservableTwoReplicaPairWeight D source.1)
                (sources.filter (fun source =>
                  decide (terminalCode first = terminalCode source))) := by
          apply listQSum_filter_le_filter
          · intro source
            exact slabObservableTwoReplicaPairWeight_nonnegative
              D rootFaceId source.1
          · intro source hsource
            have hsourceEq : target = repair source :=
              of_decide_eq_true hsource
            have hpackEq : data.pack (terminalCode source) =
                data.pack (terminalCode first) := by
              exact hsourceEq.symm.trans hfirstEq
            have hterminal := data.pack_injective
              (terminalCode source) (terminalCode first) hpackEq
            exact decide_eq_true hterminal.symm
        have hfiberBound :
            fiberWeight sources
                (fun source => slabObservableTwoReplicaPairWeight D source.1)
                repair target ≤
              slabObservablePairedSupportGlobalAnchorRate
                    D rootFaceId targetFaceId *
                slabAcceptedTwoReplicaStateWeight cutoff half
                  (terminalCode first) := by
          unfold fiberWeight
          exact Q'.le_trans' _ _ _ hfilter
            (slabObservablePairedConnectedCanonicalTerminal_fiberWeight_le
              cutoff half rootFaceId targetFaceId htarget
                (terminalCode first))
        have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ rho
          hfiberBound (Q'.le_of_lt rho_pos)
        have hreassociate :
            rho *
                (slabObservablePairedSupportGlobalAnchorRate
                    D rootFaceId targetFaceId *
                  slabAcceptedTwoReplicaStateWeight cutoff half
                    (terminalCode first)) ≈
              (rho * slabObservablePairedSupportGlobalAnchorRate
                  D rootFaceId targetFaceId) *
                slabAcceptedTwoReplicaStateWeight cutoff half
                  (terminalCode first) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv rho
            (slabObservablePairedSupportGlobalAnchorRate
              D rootFaceId targetFaceId)
            (slabAcceptedTwoReplicaStateWeight cutoff half
              (terminalCode first)))
        have hterminalNonnegative :=
          slabAcceptedTwoReplicaStateWeight_nonnegative
            cutoff half (terminalCode first)
        have hbudget := Q'.mul_le_mul_of_nonneg_right _ _
          (slabAcceptedTwoReplicaStateWeight cutoff half
            (terminalCode first)) rate_budget hterminalNonnegative
        have hinsertion := data.weight_floor (terminalCode first)
        change rho * fiberWeight sources
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            repair target ≤ _
        exact Q'.le_trans' _ _ _ hscaled
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate)
            (Q'.le_trans' _ _ _ hbudget
              (by
                rw [hfirstEq]
                exact hinsertion)))

#print axioms slabObservablePairedConnectedCanonicalTerminal
#print axioms slabObservablePairedConnectedSourceEntry_mem_connectedEntries
#print axioms slabObservablePairedConnectedCanonicalTerminal_fiberWeight_le
#print axioms slabObservablePairedConnectedCanonicalPackedRepair
#print axioms SlabObservablePairedConnectedGoodTerminalPacking.toFiberRepair

end YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
