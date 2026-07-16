/-
# Canonical six-valent resolver as an exact Haar moment

The maximal four-dimensional link valence resolves into four trivalent
vertices and three internal channels.  Its middle channel separates the
graph into two exact three-leg fusion packets.  Nine constructive Fubini
steps expose that contraction, after which lossless packet synthesis gives
the six-character Haar moment.
-/

import YMGap.Continuum.Z4CanonicalFiveValentGraphHaar

namespace YMGap.Continuum.Z4CanonicalSixValentGraphHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalFiveValentGraphHaar
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge
open YMGap.Continuum.Z4VertexCartesianVacuumRemoval

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The maximal-valence resolver and its nine-fold sum -/

def sixValentGraphEdges : List Nat := [0, 1, 7, 2, 8, 3, 9, 4, 5]

def sixValentGraphVertices : List TrivalentVertex :=
  fuseLabels 6 7 (List.range 6)

theorem sixValentGraphVertices_exact :
    sixValentGraphVertices =
      [(0, 1, 7), (7, 2, 8), (8, 3, 9), (9, 4, 5)] := by
  rfl

def sixValentGraphPackets {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) := fun edge =>
  if edge < 6 then facePacketAtLinkCutoff P
  else allOnesPacket (linkAuxiliaryCutoff K)

def sixValentVertexCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  vertexCartesianSum sixValentGraphEdges sixValentGraphVertices
    (sixValentGraphPackets P)

private theorem canonicalSix_edge_order :
    [0, 1, 2, 3, 4, 5, 7, 8, 9].Perm sixValentGraphEdges := by
  have h7 : [2, 3, 4, 5, 7, 8, 9].Perm
      [7, 2, 3, 4, 5, 8, 9] := by
    simpa using
      (List.perm_append_singleton 7 [2, 3, 4, 5]).append_right [8, 9]
  have h8 : [7, 2, 3, 4, 5, 8, 9].Perm
      [7, 2, 8, 3, 4, 5, 9] := by
    simpa using
      ((List.perm_append_singleton 8 [3, 4, 5]).append_left [7, 2]).append_right [9]
  have h9 : [7, 2, 8, 3, 4, 5, 9].Perm
      [7, 2, 8, 3, 9, 4, 5] := by
    simpa using
      (List.perm_append_singleton 9 [4, 5]).append_left [7, 2, 8, 3]
  exact ((h7.trans h8).trans h9).append_left [0, 1]

private theorem canonicalSix_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ sixValentGraphEdges →
    canonicalLinkGraphPacket P 6 edge = sixValentGraphPackets P edge := by
  intro edge hedge
  simp only [sixValentGraphEdges, List.mem_cons, List.not_mem_nil,
    or_false] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [canonicalLinkGraphPacket, sixValentGraphPackets]

theorem canonicalUsed_six_eq_graph {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 6 ≈
      sixValentVertexCartesianSum P := by
  refine Q'.eqv_trans _
    (vertexCartesianSum sixValentGraphEdges sixValentGraphVertices
      (canonicalLinkGraphPacket P 6)) _ ?_ ?_
  · exact vertexCartesianSum_edge_perm sixValentGraphVertices
      (canonicalLinkGraphPacket P 6) canonicalSix_edge_order
  · exact Q'.eqv_of_eq (vertexCartesianSum_packet_eq_on
      sixValentGraphEdges sixValentGraphVertices
      (canonicalLinkGraphPacket P 6) (sixValentGraphPackets P)
      (canonicalSix_packet_agrees P))

def sixValentCartesianTerm {K : Nat} (P : CharacterPacket K)
    (a b u c channel d v e f : Nat) : Q' :=
  if fusionOK a b u = true then
    if fusionOK u c channel = true then
      if fusionOK channel d v = true then
        if fusionOK v e f = true then
          coeffAt (facePacketAtLinkCutoff P) a *
            (coeffAt (facePacketAtLinkCutoff P) b *
              (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) u *
                (coeffAt (facePacketAtLinkCutoff P) c *
                  (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) channel *
                    (coeffAt (facePacketAtLinkCutoff P) d *
                      (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) v *
                        (coeffAt (facePacketAtLinkCutoff P) e *
                          (coeffAt (facePacketAtLinkCutoff P) f * 1))))))))
        else 0
      else 0
    else 0
  else 0

def sixValentExplicitCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  let N := linkAuxiliaryCutoff K + 1
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    fsum (fun channel => fsum (fun d => fsum (fun v => fsum (fun e =>
      fsum (fun f => sixValentCartesianTerm P a b u c channel d v e f)
        N) N) N) N) N) N) N) N) N

theorem sixValentVertexSum_eq_explicit {K : Nat}
    (P : CharacterPacket K) :
    sixValentVertexCartesianSum P ≈
      sixValentExplicitCartesianSum P := by
  unfold sixValentVertexCartesianSum sixValentGraphEdges
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 0 [1, 7, 2, 8, 3, 9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 1 [7, 2, 8, 3, 9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 7 [2, 8, 3, 9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro u
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 2 [8, 3, 9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 8 [3, 9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro channel
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 3 [9, 4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 9 [4, 5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro v
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 4 [5] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro e
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 5 [] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro f
  change listQSum _ [zeroEdgeLabelling] ≈
    sixValentCartesianTerm P a b u c channel d v e f
  change graphVertexProject sixValentGraphVertices
      (packetGraphBareAmplitude [0, 1, 7, 2, 8, 3, 9, 4, 5]
        (sixValentGraphPackets P))
      (setEdgeLabel
        (setEdgeLabel
          (setEdgeLabel
            (setEdgeLabel
              (setEdgeLabel
                (setEdgeLabel
                  (setEdgeLabel
                    (setEdgeLabel
                      (setEdgeLabel zeroEdgeLabelling 5 f) 4 e) 9 v) 3 d)
                    8 channel) 2 c) 7 u) 1 b) 0 a) +
      0 ≈ sixValentCartesianTerm P a b u c channel d v e f
  rw [sixValentGraphVertices_exact]
  unfold graphVertexProject verticesAdmissibleB packetGraphBareAmplitude
    eliminateLinks sixValentGraphPackets sixValentCartesianTerm
  by_cases h1 : fusionOK a b u = true
  · by_cases h2 : fusionOK u c channel = true
    · by_cases h3 : fusionOK channel d v = true
      · by_cases h4 : fusionOK v e f = true
        · simp [setEdgeLabel, verticesAdmissibleB, eliminateLinks,
            h1, h2, h3, h4]
          exact q_add_zero_eqv _
        · simp [setEdgeLabel, verticesAdmissibleB, h1, h2, h3, h4]
          exact q_zero_add_eqv 0
      · simp [setEdgeLabel, verticesAdmissibleB, h1, h2, h3]
        exact q_zero_add_eqv 0
    · simp [setEdgeLabel, verticesAdmissibleB, h1, h2]
      exact q_zero_add_eqv 0
  · simp [setEdgeLabel, h1]
    exact q_zero_add_eqv 0

/-! ## 2. Split the nine-fold sum at the middle channel -/

def rightTripleSum (N : Nat)
    (right : Nat → Nat → Nat → Nat → Nat → Q')
    (channel : Nat) : Q' :=
  fourVariableSum N (fun d v e f => right d v e f channel)

def nineFoldProductSum (N : Nat)
    (left right : Nat → Nat → Nat → Nat → Nat → Q') : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    fsum (fun channel => fsum (fun d => fsum (fun v => fsum (fun e =>
      fsum (fun f => left a b u c channel * right d v e f channel)
        N) N) N) N) N) N) N) N) N

theorem fourVariableSum_const_mul (N : Nat) (q : Q')
    (f : Nat → Nat → Nat → Nat → Q') :
    q * fourVariableSum N f ≈
      fourVariableSum N (fun a b u c => q * f a b u c) := by
  unfold fourVariableSum
  refine Q'.eqv_trans _
    (fsum (fun a => q *
      fsum (fun b => fsum (fun u => fsum (fun c => f a b u c) N) N) N)
      N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q _ N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _
    (fsum (fun b => q *
      fsum (fun u => fsum (fun c => f a b u c) N) N) N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q _ N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _
    (fsum (fun u => q * fsum (fun c => f a b u c) N) N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q _ N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro u
  exact YMGap.Continuum.CubeRatioBounds.fsum_const_mul q
    (fun c => f a b u c) N

/-- A four-variable contraction on each side of one common channel factors
as the channelwise product of the two partial contractions. -/
theorem nineFoldProductSum_factor (N : Nat)
    (left right : Nat → Nat → Nat → Nat → Nat → Q') :
    nineFoldProductSum N left right ≈
      fsum (fun channel =>
        leftTripleSum N left channel * rightTripleSum N right channel) N := by
  unfold nineFoldProductSum
  let g := fun a b u c channel =>
    left a b u c channel * rightTripleSum N right channel
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
      fsum (fun channel => g a b u c channel) N) N) N) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro a
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro b
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro u
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro c
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro channel
    change fourVariableSum N (fun d v e f =>
        left a b u c channel * right d v e f channel) ≈
      left a b u c channel * rightTripleSum N right channel
    exact Q'.eqv_symm
      (fourVariableSum_const_mul N (left a b u c channel)
        (fun d v e f => right d v e f channel))
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun channel =>
        fsum (fun c => g a b u c channel) N) N) N) N) N) _ ?_ ?_
    · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro a
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro b
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro u
      exact YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun c channel => g a b u c channel) N N
    · refine Q'.eqv_trans _
        (fsum (fun a => fsum (fun b => fsum (fun channel =>
          fsum (fun u => fsum (fun c => g a b u c channel) N) N) N) N) N) _
        ?_ ?_
      · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro a
        apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro b
        exact YMGap.Continuum.CubeRatioBounds.fsum_swap
          (fun u channel => fsum (fun c => g a b u c channel) N) N N
      · refine Q'.eqv_trans _
          (fsum (fun a => fsum (fun channel => fsum (fun b =>
            fsum (fun u => fsum (fun c => g a b u c channel) N) N) N) N) N) _
          ?_ ?_
        · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          intro a
          exact YMGap.Continuum.CubeRatioBounds.fsum_swap
            (fun b channel =>
              fsum (fun u => fsum (fun c => g a b u c channel) N) N)
            N N
        · refine Q'.eqv_trans _
            (fsum (fun channel => fsum (fun a => fsum (fun b =>
              fsum (fun u => fsum (fun c => g a b u c channel) N) N) N) N) N) _
            (YMGap.Continuum.CubeRatioBounds.fsum_swap
              (fun a channel => fsum (fun b =>
                fsum (fun u => fsum (fun c => g a b u c channel) N) N) N)
              N N) ?_
          apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          intro channel
          change fourVariableSum N
              (fun a b u c => left a b u c channel *
                rightTripleSum N right channel) ≈
            leftTripleSum N left channel * rightTripleSum N right channel
          exact Q'.eqv_symm
            (fourVariableSum_mul_const N
              (fun a b u c => left a b u c channel)
              (rightTripleSum N right channel))

def sixRightFirstTerm {K : Nat} (P : CharacterPacket K)
    (channel d v : Nat) : Q' :=
  if fusionOK channel d v = true then
    coeffAt (facePacketAtLinkCutoff P) d
  else 0

def sixRightTripleTerm {K : Nat} (P : CharacterPacket K)
    (d v e f channel : Nat) : Q' :=
  if fusionOK channel d v = true then
    if fusionOK v e f = true then
      coeffAt (facePacketAtLinkCutoff P) d *
        (coeffAt (facePacketAtLinkCutoff P) e *
          coeffAt (facePacketAtLinkCutoff P) f)
    else 0
  else 0

private theorem six_coeff_reassociate (A B C D E F : Q') :
    A * (B * (1 * (C * (1 * (D * (1 * (E * (F * 1)))))))) ≈
      ((A * B) * C) * (D * (E * F)) := by
  refine Q'.eqv_trans _
    (A * (B * (1 * (C * (1 * (D * (1 * (E * F)))))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.mul_eqv_congr_left _ _ _
                  (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv F))))))))
  · refine Q'.eqv_trans _
      (A * (B * (1 * (C * (1 * (D * (E * F))))))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (E * F)))))))
    · refine Q'.eqv_trans _
        (A * (B * (1 * (C * (D * (E * F)))))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (D * (E * F))))))
      · refine Q'.eqv_trans _
          (A * (B * (C * (D * (E * F))))) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.one_mul_eqv (C * (D * (E * F)))))
        · refine Q'.eqv_trans _
            ((A * B) * (C * (D * (E * F)))) _
            (Q'.eqv_symm (Q'.mul_assoc_eqv A B (C * (D * (E * F))))) ?_
          exact Q'.eqv_symm (Q'.mul_assoc_eqv (A * B) C (D * (E * F)))

theorem sixValentTerm_eq_sharedProduct
    {K a b u c channel d v e f : Nat} (P : CharacterPacket K)
    (hu : u < linkAuxiliaryCutoff K + 1)
    (hchannel : channel < linkAuxiliaryCutoff K + 1)
    (hv : v < linkAuxiliaryCutoff K + 1) :
    sixValentCartesianTerm P a b u c channel d v e f ≈
      fiveLeftTripleTerm P a b u c channel *
        sixRightTripleTerm P d v e f channel := by
  have hu1 := coeffAt_allOnesPacket hu
  have hchannel1 := coeffAt_allOnesPacket hchannel
  have hv1 := coeffAt_allOnesPacket hv
  by_cases h1 : fusionOK a b u = true
  · by_cases h2 : fusionOK u c channel = true
    · by_cases h3 : fusionOK channel d v = true
      · by_cases h4 : fusionOK v e f = true
        · unfold sixValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
            graphLeftTerm sixRightTripleTerm
          rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4,
            if_pos h1, if_pos h2, if_pos h3, if_pos h4,
            hu1, hchannel1, hv1]
          exact six_coeff_reassociate _ _ _ _ _ _
        · unfold sixValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
            graphLeftTerm sixRightTripleTerm
          rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4,
            if_pos h1, if_pos h2, if_pos h3, if_neg h4]
          exact Q'.eqv_symm (Q'.mul_zero_eqv _)
      · unfold sixValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
          graphLeftTerm sixRightTripleTerm
        rw [if_pos h1, if_pos h2, if_neg h3,
          if_pos h1, if_pos h2, if_neg h3]
        exact Q'.eqv_symm (Q'.mul_zero_eqv _)
    · unfold sixValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
        graphLeftTerm
      rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
      exact Q'.eqv_symm
        (Q'.eqv_trans _ (0 * sixRightTripleTerm P d v e f channel) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_zero_eqv
              (coeffAt (facePacketAtLinkCutoff P) a *
                coeffAt (facePacketAtLinkCutoff P) b)))
          (Q'.zero_mul_eqv _))
  · unfold sixValentCartesianTerm fiveLeftTripleTerm graphLeftTerm
    rw [if_neg h1, if_neg h1]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (0 * sixRightTripleTerm P d v e f channel) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.zero_mul_eqv _))

theorem sixValentExplicit_eq_nineFold {K : Nat}
    (P : CharacterPacket K) :
    sixValentExplicitCartesianSum P ≈
      nineFoldProductSum (linkAuxiliaryCutoff K + 1)
        (fiveLeftTripleTerm P) (sixRightTripleTerm P) := by
  unfold sixValentExplicitCartesianSum nineFoldProductSum
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro u hu
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro channel hchannel
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro v hv
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro e
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro f
  exact sixValentTerm_eq_sharedProduct P hu hchannel hv

/-! ## 3. The right three-leg partial contraction -/

private theorem sixRightTripleTerm_eq_chainProduct
    {K d v e f channel : Nat} (P : CharacterPacket K) :
    sixRightTripleTerm P d v e f channel ≈
      sixRightFirstTerm P channel d v * graphRightTerm P e f v := by
  by_cases h3 : fusionOK channel d v = true
  · by_cases h4 : fusionOK v e f = true
    · unfold sixRightTripleTerm sixRightFirstTerm graphRightTerm
      rw [if_pos h3, if_pos h4, if_pos h3, if_pos h4]
      exact Q'.eqv_refl _
    · unfold sixRightTripleTerm sixRightFirstTerm graphRightTerm
      rw [if_pos h3, if_neg h4, if_pos h3, if_neg h4]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  · unfold sixRightTripleTerm sixRightFirstTerm
    rw [if_neg h3, if_neg h3]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

private theorem twoVariable_const_factor (N : Nat) (q : Q')
    (f : Nat → Nat → Q') :
    fsum (fun e => fsum (fun x => q * f e x) N) N ≈
      q * fsum (fun e => fsum (fun x => f e x) N) N := by
  refine Q'.eqv_trans _
    (fsum (fun e => q * fsum (fun x => f e x) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro e
    exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q (fun x => f e x) N)
  · exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul q
        (fun e => fsum (fun x => f e x) N) N)

theorem sixRightTripleSum_eq_pairFactor {K channel : Nat}
    (P : CharacterPacket K) :
    rightTripleSum (linkAuxiliaryCutoff K + 1)
        (sixRightTripleTerm P) channel ≈
      fsum (fun d => fsum (fun v =>
        sixRightFirstTerm P channel d v *
          rightPairSum (linkAuxiliaryCutoff K + 1) (graphRightTerm P) v)
        (linkAuxiliaryCutoff K + 1))
        (linkAuxiliaryCutoff K + 1) := by
  let N := linkAuxiliaryCutoff K + 1
  unfold rightTripleSum fourVariableSum
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro v
  refine Q'.eqv_trans _
    (fsum (fun e => fsum (fun f =>
      sixRightFirstTerm P channel d v * graphRightTerm P e f v) N) N) _
    ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro e
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro f
    exact sixRightTripleTerm_eq_chainProduct P
  · exact twoVariable_const_factor N
      (sixRightFirstTerm P channel d v)
      (fun e f => graphRightTerm P e f v)

private theorem fusionOK_right_rotate (channel d v : Nat) :
    fusionOK channel d v = fusionOK d v channel := by
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab channel d v,
    YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_bt d channel v]

private theorem sixRightFirstTerm_eq_fusionFactor
    {K channel d v : Nat} (P : CharacterPacket K) :
    sixRightFirstTerm P channel d v ≈
      fusionInd d v channel * coeffAt (facePacketAtLinkCutoff P) d := by
  unfold sixRightFirstTerm fusionInd
  rw [fusionOK_right_rotate channel d v]
  by_cases h : fusionOK d v channel = true
  · rw [if_pos h, if_pos h]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

theorem sixRightTripleSum_eq_fusionCoeff {K channel : Nat}
    (P : CharacterPacket K) :
    rightTripleSum (linkAuxiliaryCutoff K + 1)
        (sixRightTripleTerm P) channel ≈
      fusionCoeff (facePacketAtLinkCutoff P)
        (truncatedFusionPacket
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)) channel := by
  let N := linkAuxiliaryCutoff K + 1
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  refine Q'.eqv_trans _
    (fsum (fun d => fsum (fun v =>
      sixRightFirstTerm P channel d v *
        rightPairSum N (graphRightTerm P) v) N) N) _
    (sixRightTripleSum_eq_pairFactor P) ?_
  unfold fusionCoeff fusionProduct
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro v hv
  have hfirst := sixRightFirstTerm_eq_fusionFactor
    (P := P) (channel := channel) (d := d) (v := v)
  have hpair := rightPairSum_eq_fusionCoeff (P := P) (channel := v)
  have hcoeff : coeffAt T2 v = fusionCoeff F F v := by
    rw [coeffAt_of_lt T2 hv]
    rfl
  rw [hcoeff]
  exact Q'.eqv_trans _
    ((fusionInd d v channel * coeffAt F d) * fusionCoeff F F v) _
    (qmul_congr hfirst hpair)
    (Q'.mul_assoc_eqv _ _ _)

/-! ## 4. Diagonal contraction and the exact six-character Haar value -/

theorem sixValentExplicit_eq_fusionDiagonal {K : Nat}
    (P : CharacterPacket K) :
    sixValentExplicitCartesianSum P ≈
      let F := facePacketAtLinkCutoff P
      let T2 := truncatedFusionPacket F F
      let T3L := truncatedFusionPacket T2 F
      let T3R := truncatedFusionPacket F T2
      fsum (fun channel => coeffAt T3L channel * coeffAt T3R channel)
        (linkAuxiliaryCutoff K + 1) := by
  let N := linkAuxiliaryCutoff K + 1
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3L := truncatedFusionPacket T2 F
  let T3R := truncatedFusionPacket F T2
  refine Q'.eqv_trans _
    (nineFoldProductSum N (fiveLeftTripleTerm P) (sixRightTripleTerm P)) _
    (sixValentExplicit_eq_nineFold P) ?_
  refine Q'.eqv_trans _
    (fsum (fun channel =>
      leftTripleSum N (fiveLeftTripleTerm P) channel *
        rightTripleSum N (sixRightTripleTerm P) channel) N) _
    (nineFoldProductSum_factor N (fiveLeftTripleTerm P)
      (sixRightTripleTerm P)) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro channel hchannel
  have hleft := fiveLeftTripleSum_eq_fusionCoeff
    (P := P) (output := channel)
  have hright := sixRightTripleSum_eq_fusionCoeff
    (P := P) (channel := channel)
  have hT3L : coeffAt T3L channel = fusionCoeff T2 F channel := by
    rw [coeffAt_of_lt T3L hchannel]
    rfl
  have hT3R : coeffAt T3R channel = fusionCoeff F T2 channel := by
    rw [coeffAt_of_lt T3R hchannel]
    rfl
  rw [hT3L, hT3R]
  exact qmul_congr hleft hright

theorem sixValentExplicit_eq_fusionHaar {K : Nat}
    (P : CharacterPacket K) :
    sixValentExplicitCartesianSum P ≈
      let F := facePacketAtLinkCutoff P
      let T2 := truncatedFusionPacket F F
      let T3L := truncatedFusionPacket T2 F
      let T3R := truncatedFusionPacket F T2
      fusionHaar T3L T3R := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3L := truncatedFusionPacket T2 F
  let T3R := truncatedFusionPacket F T2
  exact Q'.eqv_trans _
    (fsum (fun channel => coeffAt T3L channel * coeffAt T3R channel)
      (linkAuxiliaryCutoff K + 1)) _
    (sixValentExplicit_eq_fusionDiagonal P)
    (Q'.eqv_symm (fusionHaar_eq_diagonal T3L T3R))

theorem sixValentFusionHaar_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    let F := facePacketAtLinkCutoff P
    let T2 := truncatedFusionPacket F F
    let T3L := truncatedFusionPacket T2 F
    let T3R := truncatedFusionPacket F T2
    fusionHaar T3L T3R ≈
      bareVacuumHaar (characterPow (synthesis P) 6) := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3L := truncatedFusionPacket T2 F
  let T3R := truncatedFusionPacket F T2
  let p := synthesis P
  have hFsupport := facePacketAtLinkCutoff_supported P
  have hT2support : PacketSupportedThrough T2 (K + K) :=
    truncatedFusionPacket_supported F F hFsupport hFsupport
  have hfit2 : K + K ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hfit3 : (K + K) + K ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hF : synthesis F ≈ₚ p :=
    synthesis_padPacket (externalCutoff_le_linkAuxiliaryCutoff K) P
  have hT2raw : synthesis T2 ≈ₚ pmul (synthesis F) (synthesis F) :=
    synthesis_truncatedFusionPacket F F hFsupport hFsupport hfit2
  have hT2 : synthesis T2 ≈ₚ characterPow p 2 :=
    peqv_trans hT2raw
      (peqv_trans (pmul_congr hF hF)
        (peqv_symm (characterPow_two_product p)))
  have hpow3 : pmul (characterPow p 2) p ≈ₚ characterPow p 3 := by
    have h := characterPow_add p 2 1
    exact peqv_symm
      (peqv_trans (by simpa using h)
        (pmul_congr (peqv_refl _) (characterPow_one p)))
  have hpow3R : pmul p (characterPow p 2) ≈ₚ characterPow p 3 := by
    have h := characterPow_add p 1 2
    exact peqv_symm
      (peqv_trans (by simpa using h)
        (pmul_congr (characterPow_one p) (peqv_refl _)))
  have hT3Lraw : synthesis T3L ≈ₚ
      pmul (synthesis T2) (synthesis F) :=
    synthesis_truncatedFusionPacket T2 F hT2support hFsupport hfit3
  have hT3Rraw : synthesis T3R ≈ₚ
      pmul (synthesis F) (synthesis T2) :=
    synthesis_truncatedFusionPacket F T2 hFsupport hT2support (by
      simpa [Nat.add_comm] using hfit3)
  have hT3L : synthesis T3L ≈ₚ characterPow p 3 :=
    peqv_trans hT3Lraw
      (peqv_trans (pmul_congr hT2 hF) hpow3)
  have hT3R : synthesis T3R ≈ₚ characterPow p 3 :=
    peqv_trans hT3Rraw
      (peqv_trans (pmul_congr hF hT2) hpow3R)
  have hpow6 : pmul (characterPow p 3) (characterPow p 3) ≈ₚ
      characterPow p 6 := by
    have h := characterPow_add p 3 3
    exact peqv_symm (by simpa using h)
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis T3L) (synthesis T3R))) _ ?_ ?_
  · exact Q'.eqv_symm (barePairing_eq_fusionHaar T3L T3R)
  · exact bareVacuumHaar_congr
      (peqv_trans (pmul_congr hT3L hT3R) hpow6)

theorem canonicalUsed_six_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 6 ≈
      bareVacuumHaar (characterPow (synthesis P) 6) := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3L := truncatedFusionPacket T2 F
  let T3R := truncatedFusionPacket F T2
  exact Q'.eqv_trans _ (sixValentVertexCartesianSum P) _
    (canonicalUsed_six_eq_graph P)
    (Q'.eqv_trans _ (sixValentExplicitCartesianSum P) _
      (sixValentVertexSum_eq_explicit P)
      (Q'.eqv_trans _ (fusionHaar T3L T3R) _
        (sixValentExplicit_eq_fusionHaar P)
        (sixValentFusionHaar_eq_bareHaar P)))

end YMGap.Continuum.Z4CanonicalSixValentGraphHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixValentGraphVertices_exact
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.canonicalUsed_six_eq_graph
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixValentVertexSum_eq_explicit
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.fourVariableSum_const_mul
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.nineFoldProductSum_factor
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixValentTerm_eq_sharedProduct
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixRightTripleSum_eq_fusionCoeff
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixValentExplicit_eq_fusionDiagonal
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.sixValentFusionHaar_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalSixValentGraphHaar.canonicalUsed_six_eq_bareHaar
