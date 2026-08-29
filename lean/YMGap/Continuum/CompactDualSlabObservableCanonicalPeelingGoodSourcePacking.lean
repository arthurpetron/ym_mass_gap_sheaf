/-
# Canonical terminal packing into good observable sources

Complete component peeling already bounds the whole support-connected source
mass by

  globalRate * partition^2.

The missing geometric operation can therefore be stated without returning to
individual reconstruction traces.  It is enough to inject every accepted
paired terminal into an executable good connected source, while paying one
common insertion factor `kappa` in stationary weight.  Summing this injection
gives

  kappa * partition^2 <= goodSourceMass.

Consequently any positive `rho <= 1` satisfying

  rho * globalRate <= kappa

is a genuine good-source density.  This isolates the actual background-stable
insertion theorem needed after canonical peeling: the already-proved global
entropy code and its geometric tail do not need to be recounted.

Constructive contract: finite weighted injections and exact rational order
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourcePacking

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance packingPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. The background-stable terminal packing certificate -/

/-- A weight-controlled injection from every accepted terminal background
into the executable good connected-source carrier.  The map is the precise
place where a local disconnectable pattern must be installed without losing
the recoverable terminal background. -/
structure SlabObservablePairedConnectedGoodTerminalPacking
    (cutoff half rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half) rootFaceId targetFaceId → Bool)
    (kappa : Q') : Type where
  kappa_pos : (0 : Q') < kappa
  kappa_le_one : kappa ≤ (1 : Q')
  pack : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half) →
    SlabObservablePairedConnectedGoodSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId goodB
  pack_injective : ∀ first second, pack first = pack second → first = second
  weight_floor : ∀ terminal,
    kappa * slabAcceptedTwoReplicaStateWeight cutoff half terminal ≤
      slabObservableTwoReplicaPairWeight
        (anchorSlabPhysicalData cutoff half) (pack terminal).1.1

namespace SlabObservablePairedConnectedGoodTerminalPacking

private theorem goodSourceList_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    (slabObservablePairedConnectedGoodSourceList
      D rootFaceId targetFaceId goodB).Nodup := by
  unfold slabObservablePairedConnectedGoodSourceList
    slabObservablePairedConnectedGoodSources
  exact attach_nodup_of_nodup _
    ((slabObservablePairedConnectedStrandSources_nodup
      D rootFaceId targetFaceId).filter goodB)

private theorem goodSourceList_weight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    listQSum
        (fun source : SlabObservablePairedConnectedGoodSource
          D rootFaceId targetFaceId goodB =>
            slabObservableTwoReplicaPairWeight D source.1.1)
        (slabObservablePairedConnectedGoodSourceList
          D rootFaceId targetFaceId goodB) =
      slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB := by
  unfold slabObservablePairedConnectedGoodSourceList
    slabObservablePairedConnectedGoodSourceMass
  exact listQSum_attach
    (fun source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId =>
        slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairedConnectedGoodSources
      D rootFaceId targetFaceId goodB)

/-! ## 2. Packing terminals gives a global good-mass floor -/

/-- The terminal packing converts the exact terminal partition identity into
a lower bound for the actual executable good-source mass. -/
theorem good_mass_floor
    {cutoff half rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa : Q'}
    (data : SlabObservablePairedConnectedGoodTerminalPacking
      cutoff half rootFaceId targetFaceId goodB kappa) :
    let D := anchorSlabPhysicalData cutoff half
    kappa * (D.physicalPartition * D.physicalPartition) ≤
      slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB := by
  let D := anchorSlabPhysicalData cutoff half
  let terminals := slabAcceptedTwoReplicaStates D
  let goodSources := slabObservablePairedConnectedGoodSourceList
    D rootFaceId targetFaceId goodB
  have hinjection :
      listQSum
          (fun terminal =>
            kappa * slabAcceptedTwoReplicaStateWeight
              cutoff half terminal)
          terminals ≤
        listQSum
          (fun source : SlabObservablePairedConnectedGoodSource
            D rootFaceId targetFaceId goodB =>
              slabObservableTwoReplicaPairWeight D source.1.1)
          goodSources := by
    apply listQSum_le_of_injective
      terminals goodSources
      (fun terminal =>
        kappa * slabAcceptedTwoReplicaStateWeight cutoff half terminal)
      (fun source : SlabObservablePairedConnectedGoodSource
        D rootFaceId targetFaceId goodB =>
          slabObservableTwoReplicaPairWeight D source.1.1)
      data.pack
    · exact slabAcceptedTwoReplicaStates_nodup D
    · intro terminal _
      exact List.mem_attach _ (data.pack terminal)
    · intro first _ second _ heq
      exact data.pack_injective first second heq
    · intro terminal _
      exact data.weight_floor terminal
    · intro source _
      exact slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1.1
  have hscale :
      listQSum
          (fun terminal =>
            kappa * slabAcceptedTwoReplicaStateWeight
              cutoff half terminal)
          terminals ≈
        kappa * listQSum
          (slabAcceptedTwoReplicaStateWeight cutoff half) terminals :=
    listQSum_mul_left kappa
      (slabAcceptedTwoReplicaStateWeight cutoff half) terminals
  have hterminal := slabAcceptedTwoReplicaStates_weight_total cutoff half
  have hleft :
      kappa * (D.physicalPartition * D.physicalPartition) ≈
        listQSum
          (fun terminal =>
            kappa * slabAcceptedTwoReplicaStateWeight
              cutoff half terminal)
          terminals :=
    Q'.eqv_trans _
      (kappa * listQSum
        (slabAcceptedTwoReplicaStateWeight cutoff half) terminals) _
      (Q'.mul_eqv_congr_left kappa _ _
        (Q'.eqv_symm hterminal))
      (Q'.eqv_symm hscale)
  have hright := goodSourceList_weight
    D rootFaceId targetFaceId goodB
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hinjection
      (Q'.le_of_eqv (Q'.eqv_of_eq hright)))

/-! ## 3. Contract the peeling and packing estimates into density -/

/-- If the desired density fraction times the already-proved global peeling
rate fits inside the insertion weight floor, terminal packing supplies the
literal good-source density consumed by the SU(2) routing compiler. -/
def toDensity
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
    SlabObservablePairedConnectedGoodSourceDensity
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId goodB rho where
  rho_pos := rho_pos
  rho_le_one := rho_le_one
  good_mass_floor := by
    let D := anchorSlabPhysicalData cutoff half
    let rate := slabObservablePairedSupportGlobalAnchorRate
      D rootFaceId targetFaceId
    have hconnected :
        slabObservablePairedConnectedSourceMass
            D rootFaceId targetFaceId ≤
          rate * (D.physicalPartition * D.physicalPartition) := by
      exact
        slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
          cutoff half rootFaceId targetFaceId htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ rho
      hconnected (Q'.le_of_lt rho_pos)
    have hreassociate :
        rho *
            (rate * (D.physicalPartition * D.physicalPartition)) ≈
          (rho * rate) *
            (D.physicalPartition * D.physicalPartition) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv rho rate
        (D.physicalPartition * D.physicalPartition))
    have hpartitionNonnegative :
        (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
      Q'.mul_nonneg _ _
        (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent))
        (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent))
    have hbudget := Q'.mul_le_mul_of_nonneg_right _ _
      (D.physicalPartition * D.physicalPartition)
      rate_budget hpartitionNonnegative
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate)
        (Q'.le_trans' _ _ _ hbudget data.good_mass_floor))

/-- Terminal packing followed by the existing successful-channel routing
produces the literal retained contraction object. -/
def toRetainedContraction
    {cutoff half rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈
      slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId → Bool}
    {kappa rho eta : Q'} {channelCongestion : Nat}
    (data : SlabObservablePairedConnectedGoodTerminalPacking
      cutoff half rootFaceId targetFaceId goodB kappa)
    (rho_pos : (0 : Q') < rho)
    (rho_le_one : rho ≤ (1 : Q'))
    (rate_budget :
      rho * slabObservablePairedSupportGlobalAnchorRate
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId ≤ kappa)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId htarget goodB eta channelCongestion) :
    SlabObservablePairedSplitRetainedContraction
      (anchorSlabPhysicalData cutoff half)
      rootFaceId targetFaceId :=
  routing.toRetainedContraction
    (data.toDensity htarget rho_pos rho_le_one rate_budget)

#print axioms SlabObservablePairedConnectedGoodTerminalPacking
#print axioms SlabObservablePairedConnectedGoodTerminalPacking.good_mass_floor
#print axioms SlabObservablePairedConnectedGoodTerminalPacking.toDensity
#print axioms SlabObservablePairedConnectedGoodTerminalPacking.toRetainedContraction

end SlabObservablePairedConnectedGoodTerminalPacking

end YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourcePacking
