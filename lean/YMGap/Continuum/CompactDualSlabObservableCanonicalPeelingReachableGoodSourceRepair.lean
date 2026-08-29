/-
# Reachable canonical terminals suffice for weighted good-source repair

The terminal-fiber argument never consumes an insertion of every accepted
paired state.  Its inputs are only the canonical terminals actually produced
by connected observable sources.  This module records that exact causal
interface.

A reachable-terminal repair sends each connected source to an executable good
source.  Two sources with the same receiver need only have the same canonical
terminal, and the receiver weight need only dominate the canonical-terminal
weight of that source.  These two source-indexed laws are precisely what makes
each repair fiber a subfiber of one canonical terminal fiber.

Thus the already-proved terminal Peierls estimate still gives the literal
weighted good-source fiber repair whenever

```text
  rho * globalAnchorRate <= kappa.
```

No insertion or injectivity statement is required for accepted states outside
the reachable canonical-terminal image.  The older all-terminal packing
certificate maps constructively into this smaller interface.

Constructive contract: finite filters, exact rational order, and explicit
source-indexed repair data only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingReachableGoodSourceRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
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

local instance reachableRepairPairDecidableEq
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

/-! ## 1. The exact reachable-image certificate -/

/-- A good-source repair controlled only on canonical terminals arising from
literal connected sources.  Receiver equality must recover the terminal, not
the whole source; terminal-fiber peeling pays for all sources sharing that
terminal. -/
structure SlabObservablePairedConnectedCanonicalTerminalRepair
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool)
    (kappa : Q') : Type where
  kappa_pos : (0 : Q') < kappa
  kappa_le_one : kappa ≤ (1 : Q')
  repair : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId →
    SlabObservablePairedConnectedGoodSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId goodB
  repair_eq_implies_terminal_eq : ∀ first second,
    repair first = repair second →
      slabObservablePairedConnectedCanonicalTerminal
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget first =
        slabObservablePairedConnectedCanonicalTerminal
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget second
  weight_floor : ∀ source,
    kappa * slabAcceptedTwoReplicaStateWeight cutoff half
        (slabObservablePairedConnectedCanonicalTerminal
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget source) ≤
      slabObservableTwoReplicaPairWeight
        (anchorSlabPhysicalData cutoff half) (repair source).1.1

namespace SlabObservablePairedConnectedCanonicalTerminalRepair

/-! ## 2. The older strong certificate factors through the reachable one -/

/-- Any all-accepted-terminal packing supplies the smaller canonical-image
repair by restriction along the canonical terminal map. -/
def ofTerminalPacking
    {cutoff half rootFaceId targetFaceId : Nat}
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa : Q'}
    (data : SlabObservablePairedConnectedGoodTerminalPacking
      cutoff half rootFaceId targetFaceId goodB kappa) :
    SlabObservablePairedConnectedCanonicalTerminalRepair
      cutoff half rootFaceId targetFaceId htarget goodB kappa where
  kappa_pos := data.kappa_pos
  kappa_le_one := data.kappa_le_one
  repair := fun source => data.pack
    (slabObservablePairedConnectedCanonicalTerminal
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget source)
  repair_eq_implies_terminal_eq := by
    intro first second heq
    exact data.pack_injective _ _ heq
  weight_floor := by
    intro source
    exact data.weight_floor
      (slabObservablePairedConnectedCanonicalTerminal
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId htarget source)

/-! ## 3. Reachable repair compiles to the physical weighted fiber bound -/

/-- **Reachable-terminal weighted repair compiler.**  Source-indexed terminal
recoverability and insertion weight control are sufficient for the same
literal weighted inverse-fiber capacity as an all-terminal packing. -/
def toFiberRepair
    {cutoff half rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa rho : Q'}
    (data : SlabObservablePairedConnectedCanonicalTerminalRepair
      cutoff half rootFaceId targetFaceId htarget goodB kappa)
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
  repair := data.repair
  weighted_fiber_capacity := by
    intro target
    let D := anchorSlabPhysicalData cutoff half
    let sources := slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId
    let terminalCode := slabObservablePairedConnectedCanonicalTerminal
      D rootFaceId targetFaceId htarget
    let repair := data.repair
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
            have hrepairEq : data.repair source = data.repair first := by
              exact hsourceEq.symm.trans hfirstEq
            have hterminal := data.repair_eq_implies_terminal_eq
              source first hrepairEq
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
        have hinsertion := data.weight_floor first
        change rho * fiberWeight sources
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            repair target ≤ _
        exact Q'.le_trans' _ _ _ hscaled
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate)
            (Q'.le_trans' _ _ _ hbudget
              (by
                rw [hfirstEq]
                exact hinsertion)))

#print axioms SlabObservablePairedConnectedCanonicalTerminalRepair.ofTerminalPacking
#print axioms SlabObservablePairedConnectedCanonicalTerminalRepair.toFiberRepair

end SlabObservablePairedConnectedCanonicalTerminalRepair

end YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingReachableGoodSourceRepair
