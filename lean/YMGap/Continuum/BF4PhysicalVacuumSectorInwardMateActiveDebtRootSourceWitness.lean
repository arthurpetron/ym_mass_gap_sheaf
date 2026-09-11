/-
# The active cube root carries an accepted ordered source witness

The active root already stores an auxiliary accepted after its two positive
incident spins have been collapsed through their stretched channel.  The
generic finite-valence lift now inserts that channel behind the literal root
vertex and shifts every remaining internal coordinate.  This file specializes
the construction to the physical cube carrier.

The result is an actual auxiliary labelling accepted on the ordered source
word `left :: right :: rest`.  The same source word is also proved to be a
permutation of the production incident-spin word.  Transporting the auxiliary
itself across that permutation is deliberately left as the next compiler.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation
import YMGap.Continuum.SU2StretchedFusionWitnessLift

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2StretchedFusionWitnessLift
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. The ordered physical source word -/

def rootOrderedSourceSpins
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : List Nat :=
  rootLeftSpin carrier :: rootRightSpin carrier ::
    cubeInwardMateLinkRest K physical hK hbounded
      (cubeDebtRootIncidence carrier.word)

theorem rootProductionSpins_perm_orderedSourceSpins
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    ((slabIncidentPlaqIds 1
        (cubeDebtRootIncidence carrier.word).1.link).map physical).Perm
      (rootOrderedSourceSpins carrier) := by
  simpa [rootOrderedSourceSpins, rootLeftSpin, rootRightSpin] using
    (cubeInwardMateLinkCertificate K physical hK hbounded
      (cubeDebtRootIncidence carrier.word)).2.1

theorem rootOrderedSourceSpins_length_le_six
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootOrderedSourceSpins carrier).length ≤ 6 := by
  rw [← (rootProductionSpins_perm_orderedSourceSpins carrier).length_eq]
  simpa only [List.length_map] using
    slabIncidentPlaqIds_length_le_six 1
      (cubeDebtRootIncidence carrier.word).1.link

theorem rootOrderedSourceSpins_bounded
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SpinsBounded K (rootOrderedSourceSpins carrier) := by
  apply spinsBounded_of_perm
    (rootProductionSpins_perm_orderedSourceSpins carrier)
  exact slabIncidentSpins_bounded hbounded
    (cubeDebtRootIncidence carrier.word).1.link

theorem rootStretchedSpin_le_linkAuxiliaryCutoff
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftSpin carrier + rootRightSpin carrier ≤
      linkAuxiliaryCutoff K := by
  have hspins := rootOrderedSourceSpins_bounded carrier
  have hleft : rootLeftSpin carrier ≤ K :=
    hspins (rootLeftSpin carrier) (by
      simp [rootOrderedSourceSpins])
  have hright : rootRightSpin carrier ≤ K :=
    hspins (rootRightSpin carrier) (by
      simp [rootOrderedSourceSpins])
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

/-! ## 2. The lifted accepted source auxiliary -/

def rootSourceAuxiliary
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : EdgeLabelling :=
  stretchedFusionWitnessLift
    (rootLeftSpin carrier) (rootRightSpin carrier)
    (cubeInwardMateLinkRest K physical hK hbounded
      (cubeDebtRootIncidence carrier.word))
    carrier.rootAuxiliary

theorem rootSourceAuxiliary_mem_orderedSourceSpins
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootSourceAuxiliary carrier ∈ fusionWitnessesForSpins
      (linkAuxiliaryCutoff K) (rootOrderedSourceSpins carrier) := by
  have hcollapsed := rootAuxiliary_mem_collapsedSpins carrier
  rw [rootCollapsedSpins_eq] at hcollapsed
  exact stretchedFusionWitnessLift_mem
    (linkAuxiliaryCutoff K)
    (rootLeftSpin carrier) (rootRightSpin carrier)
    (cubeInwardMateLinkRest K physical hK hbounded
      (cubeDebtRootIncidence carrier.word))
    (rootOrderedSourceSpins_length_le_six carrier)
    (rootStretchedSpin_le_linkAuxiliaryCutoff carrier)
    carrier.rootAuxiliary hcollapsed

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.rootProductionSpins_perm_orderedSourceSpins
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.rootStretchedSpin_le_linkAuxiliaryCutoff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.rootSourceAuxiliary
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.rootSourceAuxiliary_mem_orderedSourceSpins
