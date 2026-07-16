/-
# Canonical five-valent resolver as an exact Haar moment

The five-leg production resolver has three trivalent vertices and two
internal channels.  This module first exposes its vertex-only Cartesian sum
as a literal seven-fold finite sum.  It then contracts the left three-leg
subtree and the right two-leg subtree along their common channel.  Both
subtrees are lossless at the geometric auxiliary cutoff, so the contraction
is exactly the five-character Haar moment.
-/

import YMGap.Continuum.Z4CanonicalTrivalentGraphHaar
import YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility

namespace YMGap.Continuum.Z4CanonicalFiveValentGraphHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility
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
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4CanonicalTrivalentGraphHaar
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

/-! ## 1. The literal canonical resolver block -/

def fiveValentGraphEdges : List Nat := [0, 1, 6, 2, 7, 3, 4]

def fiveValentGraphVertices : List TrivalentVertex :=
  fuseLabels 5 6 (List.range 5)

theorem fiveValentGraphVertices_exact :
    fiveValentGraphVertices = [(0, 1, 6), (6, 2, 7), (7, 3, 4)] := by
  rfl

def fiveValentGraphPackets {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) := fun edge =>
  if edge < 5 then facePacketAtLinkCutoff P
  else allOnesPacket (linkAuxiliaryCutoff K)

def fiveValentVertexCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  vertexCartesianSum fiveValentGraphEdges fiveValentGraphVertices
    (fiveValentGraphPackets P)

private theorem canonicalFive_edge_order :
    [0, 1, 2, 3, 4, 6, 7].Perm fiveValentGraphEdges := by
  have h6 : [2, 3, 4, 6, 7].Perm [6, 2, 3, 4, 7] := by
    simpa using
      (List.perm_append_singleton 6 [2, 3, 4]).append_right [7]
  have h7 : [6, 2, 3, 4, 7].Perm [6, 2, 7, 3, 4] := by
    simpa using
      (List.perm_append_singleton 7 [3, 4]).append_left [6, 2]
  exact (h6.trans h7).append_left [0, 1]

private theorem canonicalFive_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ fiveValentGraphEdges →
    canonicalLinkGraphPacket P 5 edge = fiveValentGraphPackets P edge := by
  intro edge hedge
  simp only [fiveValentGraphEdges, List.mem_cons, List.not_mem_nil,
    or_false] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [canonicalLinkGraphPacket, fiveValentGraphPackets]

theorem canonicalUsed_five_eq_graph {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 5 ≈
      fiveValentVertexCartesianSum P := by
  refine Q'.eqv_trans _
    (vertexCartesianSum fiveValentGraphEdges fiveValentGraphVertices
      (canonicalLinkGraphPacket P 5)) _ ?_ ?_
  · exact vertexCartesianSum_edge_perm fiveValentGraphVertices
      (canonicalLinkGraphPacket P 5) canonicalFive_edge_order
  · exact Q'.eqv_of_eq (vertexCartesianSum_packet_eq_on
      fiveValentGraphEdges fiveValentGraphVertices
      (canonicalLinkGraphPacket P 5) (fiveValentGraphPackets P)
      (canonicalFive_packet_agrees P))

/-! ## 2. Seven constructive finite-Fubini steps -/

def fiveValentCartesianTerm {K : Nat} (P : CharacterPacket K)
    (a b u c v d e : Nat) : Q' :=
  if fusionOK a b u = true then
    if fusionOK u c v = true then
      if fusionOK v d e = true then
        coeffAt (facePacketAtLinkCutoff P) a *
          (coeffAt (facePacketAtLinkCutoff P) b *
            (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) u *
              (coeffAt (facePacketAtLinkCutoff P) c *
                (coeffAt (allOnesPacket (linkAuxiliaryCutoff K)) v *
                  (coeffAt (facePacketAtLinkCutoff P) d *
                    (coeffAt (facePacketAtLinkCutoff P) e * 1))))))
      else 0
    else 0
  else 0

def fiveValentExplicitCartesianSum {K : Nat}
    (P : CharacterPacket K) : Q' :=
  let N := linkAuxiliaryCutoff K + 1
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    fsum (fun v => fsum (fun d => fsum (fun e =>
      fiveValentCartesianTerm P a b u c v d e) N) N) N) N) N) N) N

theorem fiveValentVertexSum_eq_explicit {K : Nat}
    (P : CharacterPacket K) :
    fiveValentVertexCartesianSum P ≈
      fiveValentExplicitCartesianSum P := by
  unfold fiveValentVertexCartesianSum fiveValentGraphEdges
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 0 [1, 6, 2, 7, 3, 4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 1 [6, 2, 7, 3, 4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 6 [2, 7, 3, 4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro u
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 2 [7, 3, 4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 7 [3, 4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro v
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 3 [4] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 4 [] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro e
  change listQSum _ [zeroEdgeLabelling] ≈
    fiveValentCartesianTerm P a b u c v d e
  change graphVertexProject fiveValentGraphVertices
      (packetGraphBareAmplitude [0, 1, 6, 2, 7, 3, 4]
        (fiveValentGraphPackets P))
      (setEdgeLabel
        (setEdgeLabel
          (setEdgeLabel
            (setEdgeLabel
              (setEdgeLabel
                (setEdgeLabel
                  (setEdgeLabel zeroEdgeLabelling 4 e) 3 d) 7 v) 2 c) 6 u) 1 b) 0 a) +
      0 ≈ fiveValentCartesianTerm P a b u c v d e
  rw [fiveValentGraphVertices_exact]
  unfold graphVertexProject verticesAdmissibleB packetGraphBareAmplitude
    eliminateLinks fiveValentGraphPackets fiveValentCartesianTerm
  by_cases h1 : fusionOK a b u = true
  · by_cases h2 : fusionOK u c v = true
    · by_cases h3 : fusionOK v d e = true
      · simp [setEdgeLabel, verticesAdmissibleB, eliminateLinks, h1, h2, h3]
        exact q_add_zero_eqv _
      · simp [setEdgeLabel, verticesAdmissibleB, h1, h2, h3]
        exact q_zero_add_eqv 0
    · simp [setEdgeLabel, verticesAdmissibleB, h1, h2]
      exact q_zero_add_eqv 0
  · simp [setEdgeLabel, h1]
    exact q_zero_add_eqv 0

/-! ## 3. Generic shared-channel factorization -/

def fourVariableSum (N : Nat)
    (f : Nat → Nat → Nat → Nat → Q') : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    f a b u c) N) N) N) N

def leftTripleSum (N : Nat)
    (left : Nat → Nat → Nat → Nat → Nat → Q')
    (channel : Nat) : Q' :=
  fourVariableSum N (fun a b u c => left a b u c channel)

def sevenFoldProductSum (N : Nat)
    (left : Nat → Nat → Nat → Nat → Nat → Q')
    (right : Nat → Nat → Nat → Q') : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    fsum (fun channel => fsum (fun d => fsum (fun e =>
      left a b u c channel * right d e channel) N) N) N) N) N) N) N

private theorem inner_pair_factor (N : Nat)
    (left : Nat → Nat → Nat → Nat → Nat → Q')
    (right : Nat → Nat → Nat → Q')
    (a b u c channel : Nat) :
    fsum (fun d => fsum (fun e =>
      left a b u c channel * right d e channel) N) N ≈
      left a b u c channel * rightPairSum N right channel := by
  refine Q'.eqv_trans _
    (fsum (fun d => left a b u c channel *
      fsum (fun e => right d e channel) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro d
    exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
        (left a b u c channel) (fun e => right d e channel) N)
  · exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
        (left a b u c channel)
        (fun d => fsum (fun e => right d e channel) N) N)

theorem fourVariableSum_mul_const (N : Nat)
    (f : Nat → Nat → Nat → Nat → Q') (q : Q') :
    fourVariableSum N f * q ≈
      fourVariableSum N (fun a b u c => f a b u c * q) := by
  unfold fourVariableSum
  refine Q'.eqv_trans _
    (fsum (fun a =>
      fsum (fun b => fsum (fun u => fsum (fun c => f a b u c) N) N) N * q)
      N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_mul_const _ q N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _
    (fsum (fun b =>
      fsum (fun u => fsum (fun c => f a b u c) N) N * q) N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_mul_const _ q N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _
    (fsum (fun u => fsum (fun c => f a b u c) N * q) N) _
    (YMGap.Continuum.CubeRatioBounds.fsum_mul_const _ q N) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro u
  exact YMGap.Continuum.CubeRatioBounds.fsum_mul_const
    (fun c => f a b u c) q N

/-- Seven finite sums sharing one channel factor into the product of the
four-variable and two-variable partial contractions. -/
theorem sevenFoldProductSum_factor (N : Nat)
    (left : Nat → Nat → Nat → Nat → Nat → Q')
    (right : Nat → Nat → Nat → Q') :
    sevenFoldProductSum N left right ≈
      fsum (fun channel =>
        leftTripleSum N left channel * rightPairSum N right channel) N := by
  unfold sevenFoldProductSum
  let g := fun a b u c channel =>
    left a b u c channel * rightPairSum N right channel
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
    exact inner_pair_factor N left right a b u c channel
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
                rightPairSum N right channel) ≈
            leftTripleSum N left channel * rightPairSum N right channel
          exact Q'.eqv_symm
            (fourVariableSum_mul_const N
              (fun a b u c => left a b u c channel)
              (rightPairSum N right channel))

/-! ## 4. Identify the two partial contractions -/

def fiveLeftNextTerm {K : Nat} (P : CharacterPacket K)
    (u c channel : Nat) : Q' :=
  if fusionOK u c channel = true then
    coeffAt (facePacketAtLinkCutoff P) c
  else 0

def fiveLeftTripleTerm {K : Nat} (P : CharacterPacket K)
    (a b u c channel : Nat) : Q' :=
  graphLeftTerm P a b u * fiveLeftNextTerm P u c channel

private theorem five_coeff_reassociate (A B C D E : Q') :
    A * (B * (1 * (C * (1 * (D * (E * 1)))))) ≈
      ((A * B) * C) * (D * E) := by
  refine Q'.eqv_trans _
    (A * (B * (1 * (C * (1 * (D * E)))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv E))))))
  · refine Q'.eqv_trans _
      (A * (B * (1 * (C * (D * E))))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (D * E)))))
    · refine Q'.eqv_trans _ (A * (B * (C * (D * E)))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (C * (D * E))))
      · refine Q'.eqv_trans _ ((A * B) * (C * (D * E))) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv A B (C * (D * E)))) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv (A * B) C (D * E))

theorem fiveValentTerm_eq_sharedProduct {K a b u c v d e : Nat}
    (P : CharacterPacket K)
    (hu : u < linkAuxiliaryCutoff K + 1)
    (hv : v < linkAuxiliaryCutoff K + 1) :
    fiveValentCartesianTerm P a b u c v d e ≈
      fiveLeftTripleTerm P a b u c v * graphRightTerm P d e v := by
  have hu1 := coeffAt_allOnesPacket hu
  have hv1 := coeffAt_allOnesPacket hv
  by_cases h1 : fusionOK a b u = true
  · by_cases h2 : fusionOK u c v = true
    · by_cases h3 : fusionOK v d e = true
      · unfold fiveValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
          graphLeftTerm graphRightTerm
        rw [if_pos h1, if_pos h2, if_pos h3, if_pos h1, if_pos h2,
          if_pos h3, hu1, hv1]
        exact five_coeff_reassociate _ _ _ _ _
      · unfold fiveValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
          graphLeftTerm graphRightTerm
        rw [if_pos h1, if_pos h2, if_neg h3, if_pos h1, if_pos h2,
          if_neg h3]
        exact Q'.eqv_symm (Q'.mul_zero_eqv _)
    · unfold fiveValentCartesianTerm fiveLeftTripleTerm fiveLeftNextTerm
        graphLeftTerm
      rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
      exact Q'.eqv_symm
        (Q'.eqv_trans _ (0 * graphRightTerm P d e v) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_zero_eqv
              (coeffAt (facePacketAtLinkCutoff P) a *
                coeffAt (facePacketAtLinkCutoff P) b)))
          (Q'.zero_mul_eqv _))
  · unfold fiveValentCartesianTerm fiveLeftTripleTerm graphLeftTerm
    rw [if_neg h1, if_neg h1]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (0 * graphRightTerm P d e v) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.zero_mul_eqv _))

theorem fiveValentExplicit_eq_sevenFold {K : Nat}
    (P : CharacterPacket K) :
    fiveValentExplicitCartesianSum P ≈
      sevenFoldProductSum (linkAuxiliaryCutoff K + 1)
        (fiveLeftTripleTerm P) (graphRightTerm P) := by
  unfold fiveValentExplicitCartesianSum sevenFoldProductSum
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro u hu
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro v hv
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro e
  exact fiveValentTerm_eq_sharedProduct P hu hv

def fourFoldChainSum (N : Nat)
    (first : Nat → Nat → Nat → Q')
    (next : Nat → Nat → Nat → Q') (output : Nat) : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun u => fsum (fun c =>
    first a b u * next u c output) N) N) N) N

theorem fourFoldChainSum_factor (N : Nat)
    (first : Nat → Nat → Nat → Q')
    (next : Nat → Nat → Nat → Q') (output : Nat) :
    fourFoldChainSum N first next output ≈
      fsum (fun u => fsum (fun c =>
        leftPairSum N first u * next u c output) N) N := by
  unfold fourFoldChainSum
  let g := fun a b u c => first a b u * next u c output
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun u => fsum (fun b =>
      fsum (fun c => g a b u c) N) N) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro a
    exact YMGap.Continuum.CubeRatioBounds.fsum_swap
      (fun b u => fsum (fun c => g a b u c) N) N N
  · refine Q'.eqv_trans _
      (fsum (fun u => fsum (fun a => fsum (fun b =>
        fsum (fun c => g a b u c) N) N) N) N) _
      (YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun a u => fsum (fun b => fsum (fun c => g a b u c) N) N)
        N N) ?_
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro u
    refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun c => fsum (fun b =>
        g a b u c) N) N) N) _ ?_ ?_
    · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro a
      exact YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun b c => g a b u c) N N
    · refine Q'.eqv_trans _
        (fsum (fun c => fsum (fun a => fsum (fun b =>
          g a b u c) N) N) N) _
        (YMGap.Continuum.CubeRatioBounds.fsum_swap
          (fun a c => fsum (fun b => g a b u c) N) N N) ?_
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro c
      change fsum (fun a => fsum (fun b =>
          first a b u * next u c output) N) N ≈
        leftPairSum N first u * next u c output
      exact Q'.eqv_symm
        (Q'.eqv_trans _
          (fsum (fun a => fsum (fun b => first a b u) N *
            next u c output) N) _
          (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
            (fun a => fsum (fun b => first a b u) N)
            (next u c output) N)
          (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
            YMGap.Continuum.CubeRatioBounds.fsum_mul_const
              (fun b => first a b u) (next u c output) N) N))

private theorem fiveLeftNextTerm_eq_fusionFactor {K u c output : Nat}
    (P : CharacterPacket K) :
    fiveLeftNextTerm P u c output ≈
      fusionInd u c output * coeffAt (facePacketAtLinkCutoff P) c := by
  unfold fiveLeftNextTerm fusionInd
  by_cases h : fusionOK u c output = true
  · rw [if_pos h, if_pos h]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

private theorem rotate_scalar (A I C : Q') :
    A * (I * C) ≈ I * (A * C) := by
  refine Q'.eqv_trans _ ((A * I) * C) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv A I C)) ?_
  refine Q'.eqv_trans _ ((I * A) * C) _
    (Q'.mul_eqv_congr_right _ _ C (Q'.mul_comm_eqv A I)) ?_
  exact Q'.mul_assoc_eqv I A C

theorem fiveLeftTripleSum_eq_fusionCoeff {K output : Nat}
    (P : CharacterPacket K) :
    leftTripleSum (linkAuxiliaryCutoff K + 1)
        (fiveLeftTripleTerm P) output ≈
      fusionCoeff
        (truncatedFusionPacket
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P))
        (facePacketAtLinkCutoff P) output := by
  let N := linkAuxiliaryCutoff K + 1
  let F := facePacketAtLinkCutoff P
  let T := truncatedFusionPacket F F
  change fourFoldChainSum N (graphLeftTerm P) (fiveLeftNextTerm P) output ≈
    fusionCoeff T F output
  refine Q'.eqv_trans _
    (fsum (fun u => fsum (fun c =>
      leftPairSum N (graphLeftTerm P) u * fiveLeftNextTerm P u c output)
      N) N) _
    (fourFoldChainSum_factor N (graphLeftTerm P)
      (fiveLeftNextTerm P) output) ?_
  unfold fusionCoeff fusionProduct
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro u hu
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  have hpair := leftPairSum_eq_fusionCoeff (P := P) (channel := u)
  have hnext := fiveLeftNextTerm_eq_fusionFactor
    (P := P) (u := u) (c := c) (output := output)
  have hcoeff : coeffAt T u = fusionCoeff F F u := by
    rw [coeffAt_of_lt T hu]
    rfl
  rw [hcoeff]
  exact Q'.eqv_trans _
    (fusionCoeff F F u *
      (fusionInd u c output * coeffAt F c)) _
    (qmul_congr hpair hnext)
    (rotate_scalar _ _ _)

/-! ## 5. The channel diagonal and the exact five-character Haar value -/

theorem fiveValentExplicit_eq_fusionDiagonal {K : Nat}
    (P : CharacterPacket K) :
    fiveValentExplicitCartesianSum P ≈
      let F := facePacketAtLinkCutoff P
      let T2 := truncatedFusionPacket F F
      let T3 := truncatedFusionPacket T2 F
      fsum (fun channel => coeffAt T3 channel * coeffAt T2 channel)
        (linkAuxiliaryCutoff K + 1) := by
  let N := linkAuxiliaryCutoff K + 1
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3 := truncatedFusionPacket T2 F
  refine Q'.eqv_trans _
    (sevenFoldProductSum N (fiveLeftTripleTerm P) (graphRightTerm P)) _
    (fiveValentExplicit_eq_sevenFold P) ?_
  refine Q'.eqv_trans _
    (fsum (fun channel =>
      leftTripleSum N (fiveLeftTripleTerm P) channel *
        rightPairSum N (graphRightTerm P) channel) N) _
    (sevenFoldProductSum_factor N (fiveLeftTripleTerm P)
      (graphRightTerm P)) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro channel hchannel
  have hleft := fiveLeftTripleSum_eq_fusionCoeff
    (P := P) (output := channel)
  have hright := rightPairSum_eq_fusionCoeff
    (P := P) (channel := channel)
  have hT3 : coeffAt T3 channel = fusionCoeff T2 F channel := by
    rw [coeffAt_of_lt T3 hchannel]
    rfl
  have hT2 : coeffAt T2 channel = fusionCoeff F F channel := by
    rw [coeffAt_of_lt T2 hchannel]
    rfl
  rw [hT3, hT2]
  exact qmul_congr hleft hright

theorem fiveValentExplicit_eq_fusionHaar {K : Nat}
    (P : CharacterPacket K) :
    fiveValentExplicitCartesianSum P ≈
      let F := facePacketAtLinkCutoff P
      let T2 := truncatedFusionPacket F F
      let T3 := truncatedFusionPacket T2 F
      fusionHaar T3 T2 := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3 := truncatedFusionPacket T2 F
  exact Q'.eqv_trans _
    (fsum (fun channel => coeffAt T3 channel * coeffAt T2 channel)
      (linkAuxiliaryCutoff K + 1)) _
    (fiveValentExplicit_eq_fusionDiagonal P)
    (Q'.eqv_symm (fusionHaar_eq_diagonal T3 T2))

theorem fiveValentFusionHaar_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    let F := facePacketAtLinkCutoff P
    let T2 := truncatedFusionPacket F F
    let T3 := truncatedFusionPacket T2 F
    fusionHaar T3 T2 ≈
      bareVacuumHaar (characterPow (synthesis P) 5) := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3 := truncatedFusionPacket T2 F
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
  have hT3raw : synthesis T3 ≈ₚ pmul (synthesis T2) (synthesis F) :=
    synthesis_truncatedFusionPacket T2 F hT2support hFsupport hfit3
  have hpow3 : pmul (characterPow p 2) p ≈ₚ characterPow p 3 := by
    have h := characterPow_add p 2 1
    exact peqv_symm
      (peqv_trans (by simpa using h)
        (pmul_congr (peqv_refl _) (characterPow_one p)))
  have hT3 : synthesis T3 ≈ₚ characterPow p 3 :=
    peqv_trans hT3raw
      (peqv_trans (pmul_congr hT2 hF) hpow3)
  have hpow5 : pmul (characterPow p 3) (characterPow p 2) ≈ₚ
      characterPow p 5 := by
    have h := characterPow_add p 3 2
    exact peqv_symm (by simpa using h)
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis T3) (synthesis T2))) _ ?_ ?_
  · exact Q'.eqv_symm (barePairing_eq_fusionHaar T3 T2)
  · exact bareVacuumHaar_congr
      (peqv_trans (pmul_congr hT3 hT2) hpow5)

theorem canonicalUsed_five_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 5 ≈
      bareVacuumHaar (characterPow (synthesis P) 5) := by
  let F := facePacketAtLinkCutoff P
  let T2 := truncatedFusionPacket F F
  let T3 := truncatedFusionPacket T2 F
  exact Q'.eqv_trans _ (fiveValentVertexCartesianSum P) _
    (canonicalUsed_five_eq_graph P)
    (Q'.eqv_trans _ (fiveValentExplicitCartesianSum P) _
      (fiveValentVertexSum_eq_explicit P)
      (Q'.eqv_trans _ (fusionHaar T3 T2) _
        (fiveValentExplicit_eq_fusionHaar P)
        (fiveValentFusionHaar_eq_bareHaar P)))

end YMGap.Continuum.Z4CanonicalFiveValentGraphHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveValentGraphVertices_exact
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.canonicalUsed_five_eq_graph
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveValentVertexSum_eq_explicit
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.sevenFoldProductSum_factor
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fourVariableSum_mul_const
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveValentTerm_eq_sharedProduct
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveLeftTripleSum_eq_fusionCoeff
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveValentExplicit_eq_fusionDiagonal
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.fiveValentFusionHaar_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalFiveValentGraphHaar.canonicalUsed_five_eq_bareHaar
