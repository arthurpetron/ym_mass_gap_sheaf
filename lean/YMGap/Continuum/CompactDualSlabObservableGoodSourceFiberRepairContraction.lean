/-
# Weighted-fiber physical repair reaches the observable face contraction

The pointwise good-source repair pays a common source-to-target ratio and a
raw repair-fiber count.  Component peeling instead supplies a weighted
inverse-fiber estimate: large reconstruction codes are individually cheaper,
and their geometric tail must be summed before any common minimum is taken.

This module specializes the weighted-fiber Peierls theorem to the literal
support-connected two-replica observable carrier.  A repair fraction `rho`
is sufficient when every good target has weighted inverse load at most
`targetWeight / rho`.  The resulting good-source density composes with the
independent same-label SU(2) channel routing, so the retained fraction is

```text
rho * eta / (channelCongestion + 1).
```

No physical weighted-fiber repair is inhabited here.  Constructive contract:
attached finite carriers, exact rational fibers, and explicit witnesses only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction
import YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair

namespace YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction.SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair
open YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair.WeightedGoodSourceFiberRepairCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance goodSourceFiberRepairPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. The physical weighted-fiber repair witness -/

/-- Every connected physical strand source is repaired into the executable
good subcarrier, with one direct bound on the complete stationary-weighted
inverse load at each good target. -/
structure SlabObservablePairedConnectedGoodSourceFiberRepair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool)
    (rho : Q') : Type where
  rho_pos : (0 : Q') < rho
  rho_le_one : rho ≤ (1 : Q')
  repair : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId →
    SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB
  weighted_fiber_capacity : ∀ target,
    rho * fiberWeight
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        repair target ≤
      slabObservableTwoReplicaPairWeight D target.1.1

namespace SlabObservablePairedConnectedGoodSourceFiberRepair

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

/-- The physical witness is the generic weighted-fiber Peierls certificate on
the literal connected and good attached carriers. -/
def toFiniteFiberRepairCertificate
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho : Q'}
    (data : SlabObservablePairedConnectedGoodSourceFiberRepair
      D rootFaceId targetFaceId goodB rho) :
    WeightedGoodSourceFiberRepairCertificate
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedConnectedGoodSourceList
        D rootFaceId targetFaceId goodB)
      (fun target => slabObservableTwoReplicaPairWeight D target.1.1)
      rho where
  rho_pos := data.rho_pos
  rho_le_one := data.rho_le_one
  goodTargets_nodup := goodSourceList_nodup
    D rootFaceId targetFaceId goodB
  repair := data.repair
  repair_mem := fun source _ => List.mem_attach _ (data.repair source)
  weighted_fiber_capacity := fun target _ =>
    data.weighted_fiber_capacity target

private theorem sourceMass_eqv_list
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum
        (fun source : SlabObservablePairedConnectedStrandSource
          D rootFaceId targetFaceId =>
            slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairedConnectedStrandSources
          D rootFaceId targetFaceId) ≈
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId := by
  apply Q'.eqv_of_eq
  unfold slabObservablePairedConnectedStrandSources
    slabObservablePairedConnectedSourceMass
  exact listQSum_attach
    (slabObservableTwoReplicaPairWeight D)
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId)

private theorem goodMass_eqv_list
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool) :
    listQSum
        (fun target : SlabObservablePairedConnectedGoodSource
          D rootFaceId targetFaceId goodB =>
            slabObservableTwoReplicaPairWeight D target.1.1)
        (slabObservablePairedConnectedGoodSourceList
          D rootFaceId targetFaceId goodB) ≈
      slabObservablePairedConnectedGoodSourceMass
        D rootFaceId targetFaceId goodB := by
  apply Q'.eqv_of_eq
  unfold slabObservablePairedConnectedGoodSourceList
    slabObservablePairedConnectedGoodSourceMass
  exact listQSum_attach
    (fun source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId =>
        slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairedConnectedGoodSources
      D rootFaceId targetFaceId goodB)

/-- Weighted target-fiber capacity constructs the exact good-source density
without a separate pointwise ratio or cardinality congestion payment. -/
def toDensity
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho : Q'}
    (data : SlabObservablePairedConnectedGoodSourceFiberRepair
      D rootFaceId targetFaceId goodB rho) :
    SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB rho where
  rho_pos := data.rho_pos
  rho_le_one := data.rho_le_one
  good_mass_floor := by
    have hrepair :=
      data.toFiniteFiberRepairCertificate.fraction_mul_sourceMass_le_goodTargetMass
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left rho _ _
          (Q'.eqv_symm
            (sourceMass_eqv_list D rootFaceId targetFaceId))))
      (Q'.le_trans' _ _ _ hrepair
        (Q'.le_of_eqv
          (goodMass_eqv_list D rootFaceId targetFaceId goodB)))

/-! ## 2. Compose weighted repair and same-label SU(2) routing -/

/-- Weighted physical repair followed by the independent successful-channel
routing reaches the retained face-contraction object. -/
def toRetainedContraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {rho eta : Q'} {channelCongestion : Nat}
    (repairData : SlabObservablePairedConnectedGoodSourceFiberRepair
      D rootFaceId targetFaceId goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta channelCongestion) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId :=
  routing.toRetainedContraction repairData.toDensity

/-- At a reflected lower face, weighted-fiber repair followed by good-source
recoupling bounds the genuine same-object relative centered face form. -/
theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    {goodB : SlabObservablePairedConnectedStrandSource D rootFaceId
      (slabFaceReflectId D.extent rootFaceId) → Bool}
    {rho eta : Q'} {channelCongestion : Nat}
    (repairData : SlabObservablePairedConnectedGoodSourceFiberRepair
      D rootFaceId (slabFaceReflectId D.extent rootFaceId) goodB rho)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hroot).1)
      goodB eta channelCongestion) :
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
    SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
      D hroot repairData.toDensity routing

#print axioms SlabObservablePairedConnectedGoodSourceFiberRepair
#print axioms SlabObservablePairedConnectedGoodSourceFiberRepair.toFiniteFiberRepairCertificate
#print axioms SlabObservablePairedConnectedGoodSourceFiberRepair.toDensity
#print axioms SlabObservablePairedConnectedGoodSourceFiberRepair.toRetainedContraction
#print axioms SlabObservablePairedConnectedGoodSourceFiberRepair.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end SlabObservablePairedConnectedGoodSourceFiberRepair

end YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
