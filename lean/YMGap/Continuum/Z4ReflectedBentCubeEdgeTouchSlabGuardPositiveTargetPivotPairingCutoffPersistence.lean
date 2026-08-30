/-
# The realized pivot carrier is stable at every cutoff

The positive selector always chooses the same component-preserving target at
the unique reflected pivot.  Decode that target at the actual ambient cutoff
and prove that its realized left auxiliary is still the explicit `(1,0)`
carrier.  This is the geometric input needed to prevent a near/far strand
crossing at the pivot after the cutoff is enlarged.

Constructive contract: finite-rank inversion, canonical witness roundtrip,
and cutoff persistence of the explicit pivot witness only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairingCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. The explicit pivot anchor at ambient cutoff -/

def reflectedBentGuardGraftPivotComponentAnchorAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabPhysicalPairRecouplingWitnessData D.cutoff
      (reflectedBentGuardGraftPivotRecouplingData D hextent state) where
  leftAuxiliary := reflectedBentPivotLeftAuxiliary
  rightAuxiliary := reflectedBentPivotRightAuxiliary
  left_mem := slabLinkFusionWitnesses_mem_of_cutoff_le hcutoff
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary
    (reflectedBentGuardGraftPivotLeftAuxiliary_mem D hextent state)
  right_mem := slabLinkFusionWitnesses_mem_of_cutoff_le hcutoff
    (reflectedBentGuardGraftRightPhysical D hextent state)
    reflectedBentSwitchPivot reflectedBentPivotRightAuxiliary
    (reflectedBentGuardGraftPivotRightAuxiliary_mem D hextent state)

theorem reflectedBentGuardGraftPivotComponentSourceAtCutoff_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalPairRecouplingProductionSource 5
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        (reflectedBentGuardGraftPivotComponentAnchorAtCutoff
          D hcutoff hextent state) =
      reflectedBentGuardGraftPivotComponentSource D hextent state := by
  rfl

/-! ## 2. Equal-rank decoding at ambient cutoff -/

theorem reflectedBentGuardGraftPivotTarget_rank_source_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (anchor : SlabPhysicalPairRecouplingWitnessData D.cutoff
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        anchor (reflectedBentGuardGraftPivotTarget D hextent state) =
      reflectedBentGuardGraftPivotComponentSource D hextent state := by
  unfold slabPhysicalPairTargetToProductionSourceAtEqualRank
  rw [reflectedBentGuardGraftPivotTarget_eq_componentRank]
  unfold reflectedBentGuardGraftPivotTargetAtComponentRank
  letI : DecidableEq
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).Source := by
    exact slabPhysicalPairRecouplingKernelPackageSourceDecidableEq 5
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
  letI : DecidableEq
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).Target := by
    exact slabPhysicalPairRecouplingTargetDecidableEq 5
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
  exact
    FiniteBistochasticQKernel.targetToSource_sourceToTargetAtEqualRank
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).kernel
      (slabPhysicalPairRecouplingProductionSource 5
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        anchor)
      (reflectedBentGuardGraftPivotTransportedTarget D hextent state)
      (slabPhysicalPairRecouplingKernelPackageFive_targets_nodup
        (reflectedBentGuardGraftPivotRecouplingData D hextent state))
      (reflectedBentGuardGraftPivotComponentSource D hextent state)
      (reflectedBentGuardGraftPivotComponentSource_mem
        D hextent state)

theorem reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (anchor : SlabPhysicalPairRecouplingWitnessData D.cutoff
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)) :
    (slabPhysicalPairTargetProductionWitnessPair
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      anchor
      (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
        D hextent state)
      (reflectedBentGuardGraftPivotTarget
        D hextent state)).leftAuxiliary =
      reflectedBentPivotLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
  rw [reflectedBentGuardGraftPivotTarget_rank_source_at_cutoff]
  let realized := slabPhysicalPairProductionWitnessPairOfSource 5
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)
    anchor
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    (reflectedBentGuardGraftPivotComponentSource D hextent state)
  have hroundtrip :=
    slabPhysicalPairProductionWitnessPairOfSource_roundtrip 5
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
        D hextent state)
      anchor
      (reflectedBentGuardGraftPivotComponentSource D hextent state)
  have hsource :
      slabPhysicalPairRecouplingProductionSource 5
          (reflectedBentGuardGraftPivotRecouplingData D hextent state)
          (YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
            realized) =
        slabPhysicalPairRecouplingProductionSource 5
          (reflectedBentGuardGraftPivotRecouplingData D hextent state)
          (reflectedBentGuardGraftPivotComponentAnchorAtCutoff
            D hcutoff hextent state) := by
    exact hroundtrip.trans
      (reflectedBentGuardGraftPivotComponentSourceAtCutoff_eq
        D hcutoff hextent state).symm
  have haux :=
    slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      (YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
        realized)
      (reflectedBentGuardGraftPivotComponentAnchorAtCutoff
        D hcutoff hextent state)
      hsource
  exact haux.1

/-! ## 3. The realized ambient pivot is the classified carrier -/

theorem reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_eq_pivot
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked =
      reflectedBentPivotLeftAuxiliary := by
  unfold reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
    reflectedBentGuardGraftLocalRealizedPairAtCutoff
    reflectedBentGuardGraftLocalTargetAtCutoff
    reflectedBentGuardGraftLocalData
    reflectedBentGuardGraftLocalAnchorAtCutoff
    reflectedBentGuardGraftLocalSourceAtCutoff
    reflectedBentGuardGraftPivotLinked
  have hdegree : 5 =
      (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).length :=
    reflectedBentSwitchPivot_degree_five.symm
  cases hdegree
  change
    (slabPhysicalPairTargetProductionWitnessPair
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      _
      (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
        D hextent state)
      (reflectedBentGuardGraftTargetForData D hextent state 5
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        rfl rfl _)).leftAuxiliary =
      reflectedBentPivotLeftAuxiliary
  rw [reflectedBentGuardGraftTargetForPivot_eq]
  exact
    reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary_at_cutoff
      D hcutoff hextent state _

#print axioms reflectedBentGuardGraftPivotComponentSourceAtCutoff_eq
#print axioms reflectedBentGuardGraftPivotTarget_rank_source_at_cutoff
#print axioms reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary_at_cutoff
#print axioms reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_eq_pivot

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairingCutoffPersistence
