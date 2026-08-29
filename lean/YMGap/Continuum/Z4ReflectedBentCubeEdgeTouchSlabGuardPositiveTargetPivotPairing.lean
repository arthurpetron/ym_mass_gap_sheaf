/-
# The realized guarded-graft pivot preserves the reflected lobes

The positive guarded-graft selector chooses the column at the written rank of
the explicit non-abelian SU(2) source at the unique reflected pivot.  This
module proves that equal-rank realization returns the already classified
`(1,0)` left carrier.

Constructive contract: finite-rank inversion, target-list nodup, and canonical
witness roundtrip only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

theorem reflectedBentGuardGraftPivotTarget_rank_source
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
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

theorem reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (anchor : SlabPhysicalPairRecouplingWitnessData 1
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)) :
    (slabPhysicalPairTargetProductionWitnessPair
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      anchor
      (reflectedBentGuardGraftLeftPhysical_bounded_five
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_five
        D hcutoff hextent state)
      (reflectedBentGuardGraftPivotTarget
        D hextent state)).leftAuxiliary =
      reflectedBentPivotLeftAuxiliary := by
  unfold slabPhysicalPairTargetProductionWitnessPair
  rw [reflectedBentGuardGraftPivotTarget_rank_source]
  let realized := slabPhysicalPairProductionWitnessPairOfSource 5
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)
    anchor
    (reflectedBentGuardGraftLeftPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftPivotComponentSource D hextent state)
  have hroundtrip :=
    slabPhysicalPairProductionWitnessPairOfSource_roundtrip 5
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      (reflectedBentGuardGraftLeftPhysical_bounded_five
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_five
        D hcutoff hextent state)
      anchor
      (reflectedBentGuardGraftPivotComponentSource D hextent state)
  have hsource :
      slabPhysicalPairRecouplingProductionSource 5
          (reflectedBentGuardGraftPivotRecouplingData D hextent state)
          (YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
            realized) =
        slabPhysicalPairRecouplingProductionSource 5
          (reflectedBentGuardGraftPivotRecouplingData D hextent state)
          (reflectedBentGuardGraftPivotComponentAnchor
            D hextent state) := by
    simpa only [reflectedBentGuardGraftPivotComponentSource] using
      hroundtrip
  have haux :=
    slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      (YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
        realized)
      (reflectedBentGuardGraftPivotComponentAnchor D hextent state)
      hsource
  exact haux.1

def reflectedBentGuardGraftPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨reflectedBentSwitchPivot,
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks⟩

theorem reflectedBentGuardGraftRealizedLeftAuxiliary_eq_pivot
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftAuxiliary D hcutoff hextent state
        reflectedBentGuardGraftPivotLinked =
      reflectedBentPivotLeftAuxiliary := by
  unfold reflectedBentGuardGraftRealizedLeftAuxiliary
    reflectedBentGuardGraftLocalRealizedPair
    reflectedBentGuardGraftLocalTarget
    reflectedBentGuardGraftLocalData
    reflectedBentGuardGraftLocalAnchor
    reflectedBentGuardGraftLocalSource
    reflectedBentGuardGraftPivotLinked
  have hdegree : 5 =
      (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).length :=
    reflectedBentSwitchPivot_degree_five.symm
  cases hdegree
  change
    (slabPhysicalPairTargetProductionWitnessPair
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
      _
      (reflectedBentGuardGraftLeftPhysical_bounded_five
        D hcutoff hextent state)
      (reflectedBentGuardGraftRightPhysical_bounded_five
        D hcutoff hextent state)
      (reflectedBentGuardGraftTargetForData D hextent state 5
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        rfl rfl _)).leftAuxiliary =
      reflectedBentPivotLeftAuxiliary
  rw [reflectedBentGuardGraftTargetForPivot_eq]
  exact reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary
    D hcutoff hextent state _

#print axioms reflectedBentGuardGraftPivotTarget_rank_source
#print axioms reflectedBentGuardGraftPivotTargetProduction_leftAuxiliary
#print axioms reflectedBentGuardGraftRealizedLeftAuxiliary_eq_pivot

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
