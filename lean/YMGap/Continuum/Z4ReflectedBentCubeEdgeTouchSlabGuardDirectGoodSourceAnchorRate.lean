/-
# The explicit anchor repair rate reaches the canonical-good contraction

The direct guarded repair and the earlier recoverable guarded repair are the
same receiver map at the cutoff-one, extent-five anchor.  The recoverable
analysis already supplies a local insertion-times-peeling rate divided by its
terminal-fiber amplification.  Attaching the proof that a receiver is in the
canonical-good subcarrier cannot enlarge an inverse fiber.

Consequently, once the named same-receiver local-positive family is supplied,
the explicit recoverable anchor rate constructs the literal weighted
good-source repair and the retained same-object contraction.  This strengthens
mere fixed-datum positivity to a structured fixed-anchor formula, but it does
not make that formula uniform in coupling, cutoff, volume, or lattice spacing.

Constructive contract: exact finite fibers, the existing local guarded-rate
estimate, and proof-forgetting monotonicity only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceRepair
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardRecoverableRepair

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceAnchorRate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableCanonicalGoodSourceRouting
open YMGap.Continuum.CompactDualSlabObservableGoodSourceCongestionContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction
open YMGap.Continuum.CompactDualSlabObservableGoodSourceFiberRepairContraction.SlabObservablePairedConnectedGoodSourceFiberRepair
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectFiniteRepair
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceRepair
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardRecoverableRepair
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor

local instance guardDirectAnchorGoodPairDecidableEq :
    DecidableEq (SlabObservableTwoReplicaPair
      reflectedBentGuardAnchorData reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq
    reflectedBentGuardAnchorData reflectedBentRootFaceId

abbrev ReflectedBentGuardAnchorLocalPositiveFamily :=
  ReflectedBentGuardDirectLocalPositiveFamily
    reflectedBentGuardAnchorData (by decide) (by decide)

/-! ## 1. The direct and recoverable receiver maps coincide -/

theorem reflectedBentGuardDirectConnectedRepair_anchor_eq
    (source : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    reflectedBentGuardDirectConnectedRepair
        reflectedBentGuardAnchorData (by decide) (by decide) source =
      reflectedBentGuardConnectedRepair source := by
  rfl

/-! ## 2. Forgetting the good proof preserves the existing fiber estimate -/

theorem goodRepair_fiberWeight_le_anchorRepair
    (family : ReflectedBentGuardAnchorLocalPositiveFamily)
    (target : SlabObservablePairedConnectedGoodSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        reflectedBentGuardAnchorData reflectedBentRootFaceId
          reflectedBentTargetFaceId)) :
    fiberWeight
        (slabObservablePairedConnectedStrandSources
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight
          reflectedBentGuardAnchorData source.1)
        family.goodRepair target ≤
      fiberWeight
        (slabObservablePairedConnectedStrandSources
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight
          reflectedBentGuardAnchorData source.1)
        reflectedBentGuardConnectedRepair target.1 := by
  apply finitePositiveMapFiberWeight_le_forgottenFiberWeight
    (slabObservablePairedConnectedStrandSources
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight
      reflectedBentGuardAnchorData source.1)
    (fun source => slabObservableTwoReplicaPairWeight_nonnegative
      reflectedBentGuardAnchorData reflectedBentRootFaceId source.1)
    family.goodRepair (fun goodTarget => goodTarget.1)
    reflectedBentGuardConnectedRepair
  intro source
  exact reflectedBentGuardDirectConnectedRepair_anchor_eq source

/-- The explicit recoverable anchor rate pays every fiber of the same repair
after its receiver has been attached to the canonical-good subcarrier. -/
theorem explicitAnchorRate_mul_goodRepairFiberWeight_le
    (family : ReflectedBentGuardAnchorLocalPositiveFamily)
    (target : SlabObservablePairedConnectedGoodSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        reflectedBentGuardAnchorData reflectedBentRootFaceId
          reflectedBentTargetFaceId)) :
    reflectedBentGuardConnectedRepairRate *
        fiberWeight
          (slabObservablePairedConnectedStrandSources
            reflectedBentGuardAnchorData reflectedBentRootFaceId
              reflectedBentTargetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight
            reflectedBentGuardAnchorData source.1)
          family.goodRepair target ≤
      slabObservableTwoReplicaPairWeight
        reflectedBentGuardAnchorData target.1.1 := by
  have hfiber := goodRepair_fiberWeight_le_anchorRepair family target
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    reflectedBentGuardConnectedRepairRate hfiber
    (Q'.le_of_lt reflectedBentGuardConnectedRepairRate_pos)
  exact Q'.le_trans' _ _ _ hscaled
    (reflectedBentGuardConnectedRepairRate_mul_fiberWeight_le target.1)

/-! ## 3. Explicit anchor good-source repair and retained contraction -/

/-- The structured recoverable rate is below the exact finite minimum used by
the direct source-to-good-target construction. -/
theorem explicitAnchorRate_le_exactGoodRepairRate
    (family : ReflectedBentGuardAnchorLocalPositiveFamily) :
    reflectedBentGuardConnectedRepairRate ≤ family.rate (by decide) := by
  unfold ReflectedBentGuardDirectLocalPositiveFamily.rate
  apply le_finitePositiveMapFiberRate_of_mul_fiberWeight_le
  · exact reflectedBentGuardConnectedRepairRate_le_one
  · intro target _
    exact explicitAnchorRate_mul_goodRepairFiberWeight_le family target

/-- The literal weighted good-source certificate with the pre-existing local
insertion/peeling/congestion rate, rather than an opaque finite minimum. -/
def toExplicitAnchorGoodSourceFiberRepair
    (family : ReflectedBentGuardAnchorLocalPositiveFamily) :
    SlabObservablePairedConnectedGoodSourceFiberRepair
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId
      (slabObservablePairedConnectedCanonicalGoodB
        reflectedBentGuardAnchorData reflectedBentRootFaceId
          reflectedBentTargetFaceId)
      reflectedBentGuardConnectedRepairRate where
  rho_pos := reflectedBentGuardConnectedRepairRate_pos
  rho_le_one := reflectedBentGuardConnectedRepairRate_le_one
  repair := family.goodRepair
  weighted_fiber_capacity :=
    explicitAnchorRate_mul_goodRepairFiberWeight_le family

/-- The explicit anchor repair rate and canonical positive-row routing reach
the retained same-object contraction object. -/
def explicitAnchorRetainedContraction
    (family : ReflectedBentGuardAnchorLocalPositiveFamily) :
    SlabObservablePairedSplitRetainedContraction
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId :=
  (toExplicitAnchorGoodSourceFiberRepair family).toRetainedContraction
    (slabObservablePairedConnectedCanonicalGoodRouting
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId (by decide))

#print axioms reflectedBentGuardDirectConnectedRepair_anchor_eq
#print axioms goodRepair_fiberWeight_le_anchorRepair
#print axioms explicitAnchorRate_mul_goodRepairFiberWeight_le
#print axioms explicitAnchorRate_le_exactGoodRepairRate
#print axioms toExplicitAnchorGoodSourceFiberRepair
#print axioms explicitAnchorRetainedContraction

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardDirectGoodSourceAnchorRate
