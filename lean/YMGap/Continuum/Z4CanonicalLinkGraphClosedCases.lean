/-
# Closed canonical graph/Haar cases at valence zero, one, and four

The unused-coordinate cylinder theorem reduces the transported canonical
resolver to its genuinely read coordinates.  This module connects the two
exceptional base shapes and the previously completed four-valent block to
that reduced presentation.  The four-valent proof also exercises the new
identifier-transport theorem: the canonical auxiliary identifier `5` is
renamed to the legacy block's identifier `4` after an exact edge permutation.
-/

import YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
import YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar

namespace YMGap.Continuum.Z4CanonicalLinkGraphClosedCases

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FourValentGraphCartesianBridge
open YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4GraphIdentifierCartesianTransport
open YMGap.Continuum.Z4SequentialGraphKernelBaseCases
open YMGap.Continuum.Z4SequentialLinkExplicitKernel
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge
open YMGap.Continuum.Z4VertexCartesianVacuumRemoval

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two exceptional base shapes -/

theorem canonicalUsed_zero_eq_zeroValent {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 0 ≈
      zeroValentVertexCartesianSum P := by
  change zeroValentVertexCartesianSum P ≈
    zeroValentVertexCartesianSum P
  exact Q'.eqv_refl _

theorem canonicalUsed_zero_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 0 ≈
      YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar
        (characterPow (synthesis P) 0) := by
  exact Q'.eqv_trans _ (zeroValentVertexCartesianSum P) _
    (canonicalUsed_zero_eq_zeroValent P)
    (Q'.eqv_trans _ (explicitSequentialKernel P 0 0) _
      (zeroValentVertexSum_eq_explicitKernel P)
      (explicitSequentialKernel_zero_eq_bareHaar P (by decide)))

private theorem canonicalOne_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ [0, 1] →
    canonicalLinkGraphPacket P 1 edge = oneValentGraphPackets P edge := by
  intro edge hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl <;>
    simp [canonicalLinkGraphPacket, oneValentGraphPackets]

theorem canonicalUsed_one_eq_oneValent {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 1 ≈
      oneValentVertexCartesianSum P := by
  have hpacket := vertexCartesianSum_packet_eq_on
    [0, 1] oneValentGraphVertices
    (canonicalLinkGraphPacket P 1) (oneValentGraphPackets P)
    (canonicalOne_packet_agrees P)
  exact Q'.eqv_of_eq (by
    change canonicalUsedVertexCartesianSum P 1 =
      vertexCartesianSum [0, 1] oneValentGraphVertices
        (oneValentGraphPackets P)
    exact hpacket)

theorem canonicalUsed_one_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 1 ≈
      YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar
        (characterPow (synthesis P) 1) := by
  exact Q'.eqv_trans _ (oneValentVertexCartesianSum P) _
    (canonicalUsed_one_eq_oneValent P)
    (Q'.eqv_trans _ (explicitSequentialKernel P 1 0) _
      (oneValentVertexSum_eq_explicitKernel P)
      (explicitSequentialKernel_zero_eq_bareHaar P (by decide)))

/-! ## 2. Canonical-to-legacy transport at valence four -/

def fourValentIdentifierRename (edge : Nat) : Nat :=
  if edge = 5 then 4 else edge

theorem fourValentIdentifierRename_edges :
    [0, 1, 5, 2, 3].map fourValentIdentifierRename =
      fourValentGraphEdges := by
  decide

theorem fourValentIdentifierRename_vertices :
    (fuseLabels 4 5 (List.range 4)).map
        (mapTrivalentVertex fourValentIdentifierRename) =
      fourValentGraphVertices := by
  decide

private theorem canonicalFour_edges_nodup : [0, 1, 5, 2, 3].Nodup := by
  decide

private theorem canonicalFour_vertices_covered :
    VerticesCoveredBy [0, 1, 5, 2, 3]
      (fuseLabels 4 5 (List.range 4)) := by
  intro v hv edge hedge
  change v ∈ [(0, 1, 5), (5, 2, 3)] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · unfold VertexContains at hedge
    rcases hedge with rfl | rfl | rfl <;> simp
  · unfold VertexContains at hedge
    rcases hedge with rfl | rfl | rfl <;> simp

private theorem canonicalFour_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ [0, 1, 5, 2, 3] →
    fourValentGraphPackets P (fourValentIdentifierRename edge) =
      canonicalLinkGraphPacket P 4 edge := by
  intro edge hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl <;>
    simp [fourValentIdentifierRename, fourValentGraphPackets,
      canonicalLinkGraphPacket]

theorem canonicalFour_reordered_eq_legacy {K : Nat}
    (P : CharacterPacket K) :
    vertexCartesianSum [0, 1, 5, 2, 3]
        (fuseLabels 4 5 (List.range 4))
        (canonicalLinkGraphPacket P 4) ≈
      fourValentVertexCartesianSum P := by
  have hinj : InjectiveOnList fourValentIdentifierRename [0, 1, 5, 2, 3] :=
    injectiveOnList_of_map_nodup fourValentIdentifierRename
      [0, 1, 5, 2, 3] (by
        rw [fourValentIdentifierRename_edges]
        exact fourValentGraphEdges_nodup)
  have htransport := vertexCartesianSum_rename
    (K := linkAuxiliaryCutoff K)
    fourValentIdentifierRename [0, 1, 5, 2, 3]
    (fuseLabels 4 5 (List.range 4))
    (canonicalLinkGraphPacket P 4) (fourValentGraphPackets P)
    hinj canonicalFour_vertices_covered (canonicalFour_packet_agrees P)
  rw [fourValentIdentifierRename_edges,
    fourValentIdentifierRename_vertices] at htransport
  exact Q'.eqv_symm htransport

private theorem canonicalFour_edge_order :
    [0, 1, 2, 3, 5].Perm [0, 1, 5, 2, 3] := by
  simpa using
    (List.perm_append_singleton 5 [2, 3]).append_left [0, 1]

theorem canonicalUsed_four_eq_legacy {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 4 ≈
      fourValentVertexCartesianSum P := by
  refine Q'.eqv_trans _
    (vertexCartesianSum [0, 1, 5, 2, 3]
      (fuseLabels 4 5 (List.range 4))
      (canonicalLinkGraphPacket P 4)) _ ?_ ?_
  · exact vertexCartesianSum_edge_perm
      (fuseLabels 4 5 (List.range 4))
      (canonicalLinkGraphPacket P 4) canonicalFour_edge_order
  · exact canonicalFour_reordered_eq_legacy P

theorem canonicalUsed_four_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 4 ≈
      YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar
        (characterPow (synthesis P) 4) := by
  exact Q'.eqv_trans _ (fourValentVertexCartesianSum P) _
    (canonicalUsed_four_eq_legacy P)
    (Q'.eqv_trans _ (canonicalSequentialLinkChannelSum P 4) _
      (fourValentVertexSum_eq_canonicalSequential P)
      (canonicalSequentialLinkChannelSum_eq_bareHaar P (by decide)))

end YMGap.Continuum.Z4CanonicalLinkGraphClosedCases

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.canonicalUsed_zero_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.canonicalUsed_one_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.fourValentIdentifierRename_edges
#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.fourValentIdentifierRename_vertices
#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.canonicalFour_reordered_eq_legacy
#print axioms YMGap.Continuum.Z4CanonicalLinkGraphClosedCases.canonicalUsed_four_eq_bareHaar
