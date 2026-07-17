import YMGap.Continuum.Z4FiniteGraphVacuumCompletion

namespace YMGap.Continuum.ScratchGraphFour

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion

local infix:50 " ≈ " => Q'.eqv

def fourEdges : List Nat := [0, 1, 4, 2, 3]
def fourVertices : List TrivalentVertex := [(0, 1, 4), (4, 2, 3)]

def fourPackets {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) := fun edge =>
  if edge < 4 then facePacketAtLinkCutoff P
  else allOnesPacket (linkAuxiliaryCutoff K)

def fourGraphSum {K : Nat} (P : CharacterPacket K) : Q' :=
  listQSum
    (graphVertexProject fourVertices
      (packetGraphBareAmplitude fourEdges (fourPackets P)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) fourEdges)

def fourCartesianTerm {K : Nat} (P : CharacterPacket K)
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

def fourCartesianSum {K : Nat} (P : CharacterPacket K) : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun channel =>
    fsum (fun c => fsum (fun d =>
      fourCartesianTerm P a b channel c d)
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1))
      (linkAuxiliaryCutoff K + 1)

theorem fourGraphSum_eq_cartesian {K : Nat} (P : CharacterPacket K) :
    fourGraphSum P ≈ fourCartesianSum P := by
  unfold fourGraphSum fourEdges
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
    fourCartesianTerm P a b channel c d
  change graphVertexProject fourVertices
      (packetGraphBareAmplitude [0, 1, 4, 2, 3] (fourPackets P))
      (setEdgeLabel
        (setEdgeLabel
          (setEdgeLabel
            (setEdgeLabel
              (setEdgeLabel zeroEdgeLabelling 3 d) 2 c) 4 channel) 1 b) 0 a) +
      0 ≈ fourCartesianTerm P a b channel c d
  unfold graphVertexProject fourVertices verticesAdmissibleB
    packetGraphBareAmplitude eliminateLinks fourPackets fourCartesianTerm
  by_cases h1 : fusionOK a b channel = true
  · by_cases h2 : fusionOK channel c d = true
    · simp [setEdgeLabel, verticesAdmissibleB, eliminateLinks, h1, h2]
      exact YMGap.Constructive.QPoly.q_add_zero_eqv _
    · simp [setEdgeLabel, verticesAdmissibleB, h1, h2]
      exact YMGap.Constructive.QPoly.q_zero_add_eqv 0
  · simp [setEdgeLabel, h1]
    exact YMGap.Constructive.QPoly.q_zero_add_eqv 0

end YMGap.Continuum.ScratchGraphFour
