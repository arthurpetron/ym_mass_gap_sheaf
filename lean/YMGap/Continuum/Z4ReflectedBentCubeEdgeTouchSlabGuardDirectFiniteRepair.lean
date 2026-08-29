/-
# A direct coupling-parametric finite fiber rate for the guarded repair

The earlier guarded-repair estimate resolves the receiver fiber into a
canonical-component fiber followed by a guard-clearing fiber.  That
factorization is useful geometrically, but its available Peierls payment is
specialized to the fixed `1/400` anchor.

At cutoff one and extent five the literal connected source carrier is finite,
and the guarded construction is already a deterministic endomap of that
carrier.  We can therefore take the exact minimum, over the whole carrier, of
target weight divided by complete inverse-fiber weight.  This gives one
strictly positive rational rate for every positive coupling, without passing
through the fixed-anchor component estimate.

The rate remains a finite-volume, cutoff-one quantity.  Its dependence on the
coupling and on the complete finite carrier is explicit; no lower bound
uniform in coupling, cutoff, volume, or lattice spacing is claimed.

Constructive contract: finite exact enumeration and strictly positive
rational weights only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectFiniteRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource

local instance guardDirectPairDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (SlabObservableTwoReplicaPair
      D reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq
    D reflectedBentRootFaceId

/-! ## 1. The direct finite endomap -/

/-- Peel the marked component to its canonical accepted terminal and graft the
fixed reflected channel into that terminal.  The result lies back in the same
connected-source carrier. -/
def reflectedBentGuardDirectConnectedRepair
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (source : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  reflectedBentGuardGraftConnectedStrandSource
    D hcutoff hextent
    (slabObservablePairedConnectedCanonicalTerminal
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
      source)

/-! ## 2. One coupling-visible exact rate -/

/-- The exact finite minimum of receiver weight divided by the complete
inverse-fiber weight of the direct guarded repair. -/
def reflectedBentGuardDirectConnectedRepairRate
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling) : Q' :=
  finitePositiveEndomapFiberRate
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (reflectedBentGuardDirectConnectedRepair D hcutoff hextent)

theorem reflectedBentGuardDirectConnectedRepairRate_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling) :
    (0 : Q') < reflectedBentGuardDirectConnectedRepairRate
      D hcutoff hextent hcoupling :=
  finitePositiveEndomapFiberRate_pos
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (reflectedBentGuardDirectConnectedRepair D hcutoff hextent)

theorem reflectedBentGuardDirectConnectedRepairRate_le_one
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling) :
    reflectedBentGuardDirectConnectedRepairRate
        D hcutoff hextent hcoupling <= (1 : Q') :=
  finitePositiveEndomapFiberRate_le_one
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (reflectedBentGuardDirectConnectedRepair D hcutoff hextent)

/-- **Coupling-parametric complete receiver-fiber estimate.**  At every
positive coupling, the direct finite rate pays the entire inverse fiber of
the literal guarded repair. -/
theorem reflectedBentGuardDirectConnectedRepairRate_mul_fiberWeight_le
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (target : SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId) :
    reflectedBentGuardDirectConnectedRepairRate
          D hcutoff hextent hcoupling *
        fiberWeight
          (slabObservablePairedConnectedStrandSources
            D reflectedBentRootFaceId reflectedBentTargetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          (reflectedBentGuardDirectConnectedRepair D hcutoff hextent)
          target <=
      slabObservableTwoReplicaPairWeight D target.1 :=
  finitePositiveEndomapFiberRate_mul_fiberWeight_le
    (slabObservablePairedConnectedStrandSources
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (fun source =>
      slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        D hcoupling source.1)
    (reflectedBentGuardDirectConnectedRepair D hcutoff hextent)
    target (List.mem_attach _ target)

#print axioms reflectedBentGuardDirectConnectedRepair
#print axioms reflectedBentGuardDirectConnectedRepairRate_pos
#print axioms reflectedBentGuardDirectConnectedRepairRate_le_one
#print axioms reflectedBentGuardDirectConnectedRepairRate_mul_fiberWeight_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectFiniteRepair
