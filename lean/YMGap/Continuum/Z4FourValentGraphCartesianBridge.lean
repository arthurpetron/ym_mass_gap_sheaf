/-
# Actual four-valent graph syntax as an explicit fusion Cartesian sum

This module crosses the first syntactic part of the finite-graph/Haar
interface.  It uses the actual `fuseLabels` resolver on four physical edge
identifiers, the enlarged `6*K` auxiliary carrier, the actual
`boundedEdgeLabellings` enumeration, and the vertex-only projector.

Five applications of constructive finite Fubini expose the graph sum as the
literal five-fold Cartesian sum over four external labels and the complete
intermediate channel.  The generic vacuum-completion theorem simultaneously
identifies this vertex-only sum with the derived zero-labelling amplitude
plus the graph's nonvacuum projected sum.

Honest scope: this proves the exact graph-syntax and normalization rewrite
for the first genuinely nontrivial local valence.  The successor theorem
must factor the displayed five-fold sum into the canonical sequential fusion
coefficient (and then repeat the syntax argument uniformly through valence
six).
-/

import YMGap.Continuum.Z4FiniteGraphVacuumCompletion

namespace YMGap.Continuum.Z4FourValentGraphCartesianBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The actual four-leg resolver block -/

def fourValentGraphEdges : List Nat := [0, 1, 4, 2, 3]

/-- The vertices are produced by the production finite-box resolver, with
edge `4` the sole intermediate channel and edge `5` the unused reserved
vacuum terminator. -/
def fourValentGraphVertices : List TrivalentVertex :=
  fuseLabels 5 4 [0, 1, 2, 3]

theorem fourValentGraphVertices_exact :
    fourValentGraphVertices = [(0, 1, 4), (4, 2, 3)] := by
  rfl

theorem fourValentGraphEdges_nodup : fourValentGraphEdges.Nodup := by
  decide

/-- Physical legs carry the zero-padded external packet; the intermediate
edge carries every channel through the enlarged auxiliary cutoff. -/
def fourValentGraphPackets {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) := fun edge =>
  if edge < 4 then facePacketAtLinkCutoff P
  else allOnesPacket (linkAuxiliaryCutoff K)

def fourValentVertexCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  listQSum
    (graphVertexProject fourValentGraphVertices
      (packetGraphBareAmplitude fourValentGraphEdges
        (fourValentGraphPackets P)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) fourValentGraphEdges)

def fourValentProjectedCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  listQSum
    (graphGaugeVacuumProject fourValentGraphEdges fourValentGraphVertices
      (packetGraphBareAmplitude fourValentGraphEdges
        (fourValentGraphPackets P)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) fourValentGraphEdges)

def fourValentVacuumCompletedProjectedSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  packetGraphBareAmplitude fourValentGraphEdges (fourValentGraphPackets P)
      zeroEdgeLabelling +
    fourValentProjectedCartesianSum P

/-- The vertex-only convention and the graph nonvacuum convention differ by
exactly the derived bare zero-labelling amplitude. -/
theorem fourValentVertexSum_eq_vacuumCompletedProjected
    {K : Nat} (P : CharacterPacket K) :
    fourValentVertexCartesianSum P ≈
      fourValentVacuumCompletedProjectedSum P := by
  exact vertexCartesianSum_eq_vacuum_add_projected
    fourValentGraphEdges fourValentGraphEdges_nodup
    fourValentGraphVertices
    (packetGraphBareAmplitude fourValentGraphEdges
      (fourValentGraphPackets P))

/-! ## 2. The literal five-fold fusion sum -/

def fourValentCartesianTerm {K : Nat} (P : CharacterPacket K)
    (a b channel c d : Nat) : Q' :=
  if fusionOK a b channel = true then
    if fusionOK channel c d = true then
      coeffAt (facePacketAtLinkCutoff P) a *
        (coeffAt (facePacketAtLinkCutoff P) b *
          (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) channel *
            (coeffAt (facePacketAtLinkCutoff P) c *
              (coeffAt (facePacketAtLinkCutoff P) d * 1))))
    else 0
  else 0

def fourValentExplicitCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun channel =>
    fsum (fun c => fsum (fun d =>
      fourValentCartesianTerm P a b channel c d)
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1)

/-- **Actual graph-syntax/Fubini bridge at valence four.** -/
theorem fourValentVertexSum_eq_explicitCartesian
    {K : Nat} (P : CharacterPacket K) :
    fourValentVertexCartesianSum P ≈
      fourValentExplicitCartesianSum P := by
  unfold fourValentVertexCartesianSum fourValentGraphEdges
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 0 [1, 4, 2, 3] _)
    ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 1 [4, 2, 3] _)
    ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 4 [2, 3] _)
    ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro channel
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 2 [3] _)
    ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 3 [] _)
    ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  change listQSum _ [zeroEdgeLabelling] ≈
    fourValentCartesianTerm P a b channel c d
  change graphVertexProject fourValentGraphVertices
      (packetGraphBareAmplitude [0, 1, 4, 2, 3]
        (fourValentGraphPackets P))
      (setEdgeLabel
        (setEdgeLabel
          (setEdgeLabel
            (setEdgeLabel
              (setEdgeLabel zeroEdgeLabelling 3 d) 2 c) 4 channel) 1 b) 0 a) +
      0 ≈ fourValentCartesianTerm P a b channel c d
  rw [fourValentGraphVertices_exact]
  unfold graphVertexProject verticesAdmissibleB packetGraphBareAmplitude eliminateLinks
    fourValentGraphPackets fourValentCartesianTerm
  by_cases h1 : fusionOK a b channel = true
  · by_cases h2 : fusionOK channel c d = true
    · simp [setEdgeLabel, verticesAdmissibleB, eliminateLinks, h1, h2]
      exact YMGap.Constructive.QPoly.q_add_zero_eqv _
    · simp [setEdgeLabel, verticesAdmissibleB, h1, h2]
      exact YMGap.Constructive.QPoly.q_zero_add_eqv 0
  · simp [setEdgeLabel, h1]
    exact YMGap.Constructive.QPoly.q_zero_add_eqv 0

end YMGap.Continuum.Z4FourValentGraphCartesianBridge

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FourValentGraphCartesianBridge.fourValentGraphVertices_exact
#print axioms YMGap.Continuum.Z4FourValentGraphCartesianBridge.fourValentGraphEdges_nodup
#print axioms YMGap.Continuum.Z4FourValentGraphCartesianBridge.fourValentVertexSum_eq_vacuumCompletedProjected
#print axioms YMGap.Continuum.Z4FourValentGraphCartesianBridge.fourValentVertexSum_eq_explicitCartesian
