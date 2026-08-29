/-
# Repair arbitrary connected sources into the recoupling-good subcarrier

The good-source contraction separates two maps which must not be conflated:

* a physical repair may change spin labels and pays a Gibbs-weight ratio;
* a successful SU(2) recoupling channel keeps those repaired physical labels
  fixed and pays its own row weight.

This module specializes the finite weighted Peierls repair theorem to the
literal support-connected observable source carrier.  A repair factor
`lambda` with congestion `repairCongestion + 1` constructs the good-source
density.  Composing it with a selected successful channel of weight `eta`
and congestion `channelCongestion + 1` gives the exact retained fraction

```text
  (lambda / (repairCongestion + 1))
    * (eta / (channelCongestion + 1)).
```

No repair map or channel family is inhabited here.  Constructive contract:
attached physical carriers, exact finite weights, and explicit fibers only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
import YMGap.Continuum.FiniteWeightedGoodSourceRepair

namespace YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction

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
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGoodSourceRepair
open YMGap.Continuum.FiniteWeightedGoodSourceRepair.WeightedGoodSourceRepairCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance goodSourceRepairPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. The physical repair witness -/

/-- Every connected physical strand source is repaired into the executable
good subcarrier.  The repair may change the physical pair, but its weight
loss and target multiplicity are both explicit. -/
structure SlabObservablePairedConnectedGoodSourceRepair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool)
    (lambda : Q') (repairCongestion : Nat) : Type where
  lambda_pos : (0 : Q') < lambda
  lambda_le_one : lambda ≤ (1 : Q')
  repair : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId →
    SlabObservablePairedConnectedGoodSource
      D rootFaceId targetFaceId goodB
  repair_weight_floor : ∀ source,
    lambda * slabObservableTwoReplicaPairWeight D source.1 ≤
      slabObservableTwoReplicaPairWeight D (repair source).1.1
  repair_fiber_count_le : ∀ target,
    (selectedTargetFiber
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (fun _ : SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId => Unit)
      (fun _ => ()) (fun source _ => repair source) target).length ≤
        repairCongestion + 1

namespace SlabObservablePairedConnectedGoodSourceRepair

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

/-- The physical repair is an instance of the generic finite weighted repair
certificate. -/
def toFiniteRepairCertificate
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {lambda : Q'} {repairCongestion : Nat}
    (data : SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId goodB lambda repairCongestion) :
    WeightedGoodSourceRepairCertificate
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedConnectedGoodSourceList
        D rootFaceId targetFaceId goodB)
      (fun target => slabObservableTwoReplicaPairWeight D target.1.1)
      lambda repairCongestion where
  lambda_pos := data.lambda_pos
  lambda_le_one := data.lambda_le_one
  goodTargets_nodup := goodSourceList_nodup
    D rootFaceId targetFaceId goodB
  sourceWeight_nonnegative := fun source _ =>
    slabObservableTwoReplicaPairWeight_nonnegative D rootFaceId source.1
  targetWeight_nonnegative := fun target _ =>
    slabObservableTwoReplicaPairWeight_nonnegative D rootFaceId target.1.1
  repair := data.repair
  repair_mem := fun source _ => List.mem_attach _ (data.repair source)
  repair_weight_floor := fun source _ => data.repair_weight_floor source
  repair_fiber_count_le := data.repair_fiber_count_le

/-- The physical good-source density produced by the repair. -/
def fraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {lambda : Q'} {repairCongestion : Nat}
    (data : SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId goodB lambda repairCongestion) : Q' :=
  data.toFiniteRepairCertificate.fraction

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

/-- The physical repair constructs the exact density certificate consumed by
the good-source recoupling theorem. -/
def toDensity
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {lambda : Q'} {repairCongestion : Nat}
    (data : SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId goodB lambda repairCongestion) :
    SlabObservablePairedConnectedGoodSourceDensity
      D rootFaceId targetFaceId goodB data.fraction where
  rho_pos := data.toFiniteRepairCertificate.fraction_pos
  rho_le_one := data.toFiniteRepairCertificate.fraction_le_one
  good_mass_floor := by
    have hrepair :=
      data.toFiniteRepairCertificate.fraction_mul_sourceMass_le_goodTargetMass
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left data.fraction _ _
          (Q'.eqv_symm
            (sourceMass_eqv_list D rootFaceId targetFaceId))))
      (Q'.le_trans' _ _ _ hrepair
        (Q'.le_of_eqv
          (goodMass_eqv_list D rootFaceId targetFaceId goodB)))

/-! ## 2. Compose physical repair and same-label SU(2) routing -/

/-- The two distinct congestion payments compose into the retained physical
face contraction. -/
def toRetainedContraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {goodB : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId → Bool}
    {lambda eta : Q'} {repairCongestion channelCongestion : Nat}
    (repairData : SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId targetFaceId goodB lambda repairCongestion)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId targetFaceId htarget goodB eta channelCongestion) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId :=
  routing.toRetainedContraction repairData.toDensity

/-- At a reflected lower face, weighted repair followed by good-source
recoupling bounds the genuine same-object relative centered face form. -/
theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    {goodB : SlabObservablePairedConnectedStrandSource D rootFaceId
      (slabFaceReflectId D.extent rootFaceId) → Bool}
    {lambda eta : Q'} {repairCongestion channelCongestion : Nat}
    (repairData : SlabObservablePairedConnectedGoodSourceRepair
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      goodB lambda repairCongestion)
    (routing : SlabObservablePairedConnectedGoodSourceSelectedChoiceCongestion
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hroot).1)
      goodB eta channelCongestion) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      ((1 : Q') + -routing.fraction repairData.fraction) *
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

#print axioms SlabObservablePairedConnectedGoodSourceRepair.toFiniteRepairCertificate
#print axioms SlabObservablePairedConnectedGoodSourceRepair.toDensity
#print axioms SlabObservablePairedConnectedGoodSourceRepair.toRetainedContraction
#print axioms SlabObservablePairedConnectedGoodSourceRepair.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end SlabObservablePairedConnectedGoodSourceRepair

end YMGap.Continuum.CompactDualSlabObservableGoodSourceRepairContraction
