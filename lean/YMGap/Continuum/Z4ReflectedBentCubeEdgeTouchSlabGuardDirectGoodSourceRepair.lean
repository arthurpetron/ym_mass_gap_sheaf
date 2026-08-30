/-
# Direct guarded repair into the canonical recoupling-good carrier

The guarded finite repair already sends every connected source to a source
whose marked strands are geometrically disconnected.  The remaining local
input is that the same repaired source carries a successful coordinatewise-
positive SU(2) target.  Package that input as a family indexed by the original
source.

Once the family is supplied, the canonical nonempty-row predicate recognizes
every repaired receiver as good.  A finite exact target-to-fiber minimum then
constructs the literal weighted good-source repair certificate, and the
existing canonical routing compiler produces the retained same-object
contraction data.

The family is an honest named frontier: this module does not claim that the
concrete guarded target has yet been sealed through Lean's large dependent
tuple.  The rate is finite-volume, cutoff-one, extent-five, and explicitly
depends on the coupling and both finite carriers; no uniformity is asserted.

Constructive contract: finite attached carriers, exact positive rational
weights, and explicit local target witnesses only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
import YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
import YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel
import YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectFiniteRepair

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction.SlabObservablePairedConnectedGoodSourceFiberRepair
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedLocalPositiveChannel
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectFiniteRepair

local instance guardDirectGoodPairDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (SlabObservableTwoReplicaPair
      D reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D reflectedBentRootFaceId

/-! ## 1. The exact remaining local family -/

/-- Every direct guarded receiver carries a successful locally positive raw
target over that very receiver. -/
structure ReflectedBentGuardDirectLocalPositiveFamily
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) : Type where
  target : ∀ source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId,
    SlabObservablePairedConnectedLocalPositiveTarget
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardDirectConnectedRepair
        D hcutoff hextent source)

namespace ReflectedBentGuardDirectLocalPositiveFamily

def positiveChannel
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    SlabObservablePairedConnectedLocalPositiveChannel
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  .mk (reflectedBentGuardDirectConnectedRepair D hcutoff hextent source)
    (family.target source)

def positiveChannelWitness
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  (family.positiveChannel source).toPositiveChannelWitness

theorem repair_canonicalGood
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    slabObservablePairedConnectedCanonicalGoodB
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardDirectConnectedRepair
        D hcutoff hextent source) = true :=
  slabObservablePairedConnectedCanonicalGoodB_true_of_positiveChannel
    (family.positiveChannelWitness source)

/-- The direct receiver, attached to the executable canonical-good
subcarrier. -/
def goodRepair
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    SlabObservablePairedConnectedGoodSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D reflectedBentRootFaceId reflectedBentTargetFaceId) :=
  ⟨reflectedBentGuardDirectConnectedRepair D hcutoff hextent source,
    List.mem_filter.mpr
      ⟨List.mem_attach _ _, family.repair_canonicalGood source⟩⟩

/-! ## 2. Exact weighted good-source fiber rate -/

def rate
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (hcoupling : (0 : Q') < D.coupling) : Q' :=
  finitePositiveMapFiberRate
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (slabObservablePairedConnectedGoodSourceList
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D reflectedBentRootFaceId reflectedBentTargetFaceId))
    (fun target => slabObservableTwoReplicaPairWeight D target.1.1)
    family.goodRepair

theorem rate_pos
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (hcoupling : (0 : Q') < D.coupling) :
    (0 : Q') < family.rate hcoupling :=
  finitePositiveMapFiberRate_pos
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (slabObservablePairedConnectedGoodSourceList
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D reflectedBentRootFaceId reflectedBentTargetFaceId))
    (fun target => slabObservableTwoReplicaPairWeight D target.1.1)
    (fun target =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling target.1.1)
    family.goodRepair

theorem rate_le_one
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (hcoupling : (0 : Q') < D.coupling) :
    family.rate hcoupling ≤ (1 : Q') :=
  finitePositiveMapFiberRate_le_one
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (slabObservablePairedConnectedGoodSourceList
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D reflectedBentRootFaceId reflectedBentTargetFaceId))
    (fun target => slabObservableTwoReplicaPairWeight D target.1.1)
    family.goodRepair

/-- The direct finite rate is already the complete weighted inverse-fiber
capacity required by the physical good-source contraction. -/
def toGoodSourceFiberRepair
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (hcoupling : (0 : Q') < D.coupling) :
    SlabObservablePairedConnectedGoodSourceFiberRepair
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        D reflectedBentRootFaceId reflectedBentTargetFaceId)
      (family.rate hcoupling) where
  rho_pos := family.rate_pos hcoupling
  rho_le_one := family.rate_le_one hcoupling
  repair := family.goodRepair
  weighted_fiber_capacity := by
    intro target
    exact finitePositiveMapFiberRate_mul_fiberWeight_le
      (slabObservablePairedConnectedStrandSources
        D reflectedBentRootFaceId reflectedBentTargetFaceId)
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (fun source =>
        slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
          D hcoupling source.1)
      (slabObservablePairedConnectedGoodSourceList
        D reflectedBentRootFaceId reflectedBentTargetFaceId
        (slabObservablePairedConnectedCanonicalGoodB
          D reflectedBentRootFaceId reflectedBentTargetFaceId))
      (fun goodTarget =>
        slabObservableTwoReplicaPairWeight D goodTarget.1.1)
      (fun goodTarget =>
        slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
          D hcoupling goodTarget.1.1)
      family.goodRepair target (List.mem_attach _ target)

/-! ## 3. Contract through canonical routing -/

def retainedContraction
    {D : SlabPhysicalData} {hcutoff : D.cutoff = 1}
    {hextent : D.extent = 5}
    (family : ReflectedBentGuardDirectLocalPositiveFamily
      D hcutoff hextent)
    (hcoupling : (0 : Q') < D.coupling) :
    SlabObservablePairedSplitRetainedContraction
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  (family.toGoodSourceFiberRepair hcoupling).toRetainedContraction
    (slabObservablePairedConnectedCanonicalGoodRouting
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (by simpa only [hextent] using reflectedBentTargetFaceId_physical))

#print axioms ReflectedBentGuardDirectLocalPositiveFamily.repair_canonicalGood
#print axioms ReflectedBentGuardDirectLocalPositiveFamily.rate_pos
#print axioms ReflectedBentGuardDirectLocalPositiveFamily.toGoodSourceFiberRepair
#print axioms ReflectedBentGuardDirectLocalPositiveFamily.retainedContraction

end ReflectedBentGuardDirectLocalPositiveFamily

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceRepair
