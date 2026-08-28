/-
# Support localization of transported old routes

The transported routing maps every old canonical path coordinatewise into the
later cutoff.  This module records the resulting geometric fact: every edge
of such a mapped path has both endpoints in the embedded-old carrier.

No quantitative estimate, completed gap, continuum limit, or Clay conclusion
is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
functional extensionality, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler

theorem matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOld
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    {first last : Nat} ->
      (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset) ->
      (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0)
        (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale cutoffOffset)
        first last) ->
      forall edge,
        edge ∈ PositiveKernelChainIn.directedEdges
          (matchedEventualCanonicalMapPositivePathToNext
            trajectory transitionStart physicalScale cutoffOffset
            hfirst path) ->
        edge.1 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset ∧
          edge.2 ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset
  | _, _, _, PositiveKernelChainIn.refl _, edge, hedge => by
      cases hedge
  | first, _, hfirst,
      PositiveKernelChainIn.step (next := next) _ hnext rest,
      edge, hedge => by
      rcases List.mem_cons.mp hedge with hhead | htail
      · subst edge
        exact
          ⟨List.mem_map.mpr ⟨first, hfirst, rfl⟩,
            List.mem_map.mpr ⟨next, hnext, rfl⟩⟩
      · exact
          matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOld
            trajectory transitionStart physicalScale cutoffOffset
            hnext rest edge htail

theorem matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOldPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {first last : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset)
      first last)
    (edge : Nat × Nat)
    (hedge : edge ∈ PositiveKernelChainIn.directedEdges
      (matchedEventualCanonicalMapPositivePathToNext
        trajectory transitionStart physicalScale cutoffOffset
        hfirst path)) :
    edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset := by
  apply (mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff
    trajectory transitionStart physicalScale cutoffOffset edge).mpr
  exact
    matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset
      hfirst path edge hedge

theorem matchedEventualCanonicalMapPositivePathToNext_avoids_newEdge
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    {first last : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset)
      first last)
    (edge : Nat × Nat)
    (hnew : edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    edge ∉ PositiveKernelChainIn.directedEdges
      (matchedEventualCanonicalMapPositivePathToNext
        trajectory transitionStart physicalScale cutoffOffset
        hfirst path) := by
  intro hedge
  exact hnew
    (matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOldPair
      trajectory transitionStart physicalScale cutoffOffset
      hfirst path edge hedge)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport.matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport.matchedEventualCanonicalMapPositivePathToNext_directedEdges_mem_embeddedOldPair
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedOldSupport.matchedEventualCanonicalMapPositivePathToNext_avoids_newEdge
