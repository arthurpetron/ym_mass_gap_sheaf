/-
# Canonical two- and three-valent graph blocks as exact Haar moments

Both remaining low-valence resolver shapes use one trivalent vertex on three
enumerated coordinates.  This file first proves a packet-generic finite
Fubini theorem for that graph.  With a normalized vacuum third packet it is
the two-character Haar pairing; with three physical packets it is the exact
three-character Haar moment through one lossless truncated fusion packet.
-/

import YMGap.Continuum.Z4CanonicalLinkGraphClosedCases

namespace YMGap.Continuum.Z4CanonicalTrivalentGraphHaar

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
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge
open YMGap.Continuum.Z4VertexCartesianVacuumRemoval

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. A packet-generic single-vertex Cartesian theorem -/

def trivalentGraphPackets {K : Nat}
    (A B C : CharacterPacket K) : Nat → CharacterPacket K :=
  fun edge => if edge = 0 then A else if edge = 1 then B else C

def trivalentVertexCartesianSum {K : Nat}
    (A B C : CharacterPacket K) : Q' :=
  vertexCartesianSum [0, 1, 2] [(0, 1, 2)]
    (trivalentGraphPackets A B C)

def trivalentCartesianTerm {K : Nat}
    (A B C : CharacterPacket K) (a b c : Nat) : Q' :=
  if fusionOK a b c = true then
    coeffAt A a * (coeffAt B b * (coeffAt C c * 1))
  else 0

def trivalentExplicitCartesianSum {K : Nat}
    (A B C : CharacterPacket K) : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun c =>
    trivalentCartesianTerm A B C a b c) (K + 1)) (K + 1)) (K + 1)

theorem trivalentVertexSum_eq_explicit {K : Nat}
    (A B C : CharacterPacket K) :
    trivalentVertexCartesianSum A B C ≈
      trivalentExplicitCartesianSum A B C := by
  unfold trivalentVertexCartesianSum vertexCartesianSum
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons K 0 [1, 2] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons K 1 [2] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons K 2 [] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  change listQSum _ [zeroEdgeLabelling] ≈
    trivalentCartesianTerm A B C a b c
  change graphVertexProject [(0, 1, 2)]
      (packetGraphBareAmplitude [0, 1, 2]
        (trivalentGraphPackets A B C))
      (setEdgeLabel
        (setEdgeLabel (setEdgeLabel zeroEdgeLabelling 2 c) 1 b) 0 a) + 0 ≈
    trivalentCartesianTerm A B C a b c
  unfold graphVertexProject verticesAdmissibleB packetGraphBareAmplitude
    eliminateLinks trivalentGraphPackets trivalentCartesianTerm
  by_cases hfusion : fusionOK a b c = true
  · simp [setEdgeLabel, hfusion]
    exact q_add_zero_eqv _
  · simp [setEdgeLabel, hfusion]
    exact q_zero_add_eqv 0

/-! ## 2. The canonical degree-two block -/

private theorem canonicalTwo_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ [0, 1, 2] →
    canonicalLinkGraphPacket P 2 edge =
      trivalentGraphPackets (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P)
        (vacuumPacket (linkAuxiliaryCutoff K)) edge := by
  intro edge hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl | rfl <;>
    simp [canonicalLinkGraphPacket, trivalentGraphPackets]

theorem canonicalUsed_two_eq_trivalent {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 2 ≈
      trivalentVertexCartesianSum
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
        (vacuumPacket (linkAuxiliaryCutoff K)) := by
  have hpacket := vertexCartesianSum_packet_eq_on
    [0, 1, 2] [(0, 1, 2)]
    (canonicalLinkGraphPacket P 2)
    (trivalentGraphPackets
      (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
      (vacuumPacket (linkAuxiliaryCutoff K)))
    (canonicalTwo_packet_agrees P)
  exact Q'.eqv_of_eq (by
    change canonicalUsedVertexCartesianSum P 2 =
      vertexCartesianSum [0, 1, 2] [(0, 1, 2)]
        (trivalentGraphPackets
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
          (vacuumPacket (linkAuxiliaryCutoff K)))
    exact hpacket)

private theorem trivalentTerm_vacuum_ne_zero {L a b c : Nat}
    (A B : CharacterPacket L) (hc : c ≠ 0) :
    trivalentCartesianTerm A B (vacuumPacket L) a b c ≈ 0 := by
  unfold trivalentCartesianTerm
  rw [coeffAt_vacuumPacket, if_neg hc]
  by_cases hfusion : fusionOK a b c = true
  · rw [if_pos hfusion]
    refine Q'.eqv_trans _
      (coeffAt A a * (coeffAt B b * 0)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 1))
    · exact Q'.eqv_trans _ (coeffAt A a * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        (Q'.mul_zero_eqv _)
  · rw [if_neg hfusion]
    exact Q'.eqv_refl 0

private theorem trivalentTerm_vacuum_zero {L a b : Nat}
    (A B : CharacterPacket L) :
    trivalentCartesianTerm A B (vacuumPacket L) a b 0 ≈
      fusionInd a b 0 * (coeffAt A a * coeffAt B b) := by
  unfold trivalentCartesianTerm fusionInd
  rw [coeffAt_vacuumPacket, if_pos rfl]
  by_cases hfusion : fusionOK a b 0 = true
  · rw [if_pos hfusion, if_pos hfusion]
    refine Q'.eqv_trans _
      (coeffAt A a * (coeffAt B b * 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1))
    · refine Q'.eqv_trans _ (coeffAt A a * coeffAt B b) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)) ?_
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · rw [if_neg hfusion, if_neg hfusion]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

theorem trivalentExplicit_vacuum_eq_fusionHaar {L : Nat}
    (A B : CharacterPacket L) :
    trivalentExplicitCartesianSum A B (vacuumPacket L) ≈
      fusionHaar A B := by
  unfold trivalentExplicitCartesianSum fusionHaar fusionCoeff fusionProduct
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  refine Q'.eqv_trans _
    (trivalentCartesianTerm A B (vacuumPacket L) a b 0) _ ?_ ?_
  · apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    · intro c hc
      exact trivalentTerm_vacuum_ne_zero A B hc
    · exact Nat.succ_pos L
  · exact trivalentTerm_vacuum_zero A B

theorem fusionHaar_facePacket_eq_degreeTwoHaar {K : Nat}
    (P : CharacterPacket K) :
    fusionHaar (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P) ≈
      bareVacuumHaar (characterPow (synthesis P) 2) := by
  let F := facePacketAtLinkCutoff P
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis F) (synthesis F))) _ ?_ ?_
  · exact Q'.eqv_symm (barePairing_eq_fusionHaar F F)
  · have hF := synthesis_padPacket
        (externalCutoff_le_linkAuxiliaryCutoff K) P
    refine Q'.eqv_trans _
      (bareVacuumHaar (pmul (synthesis P) (synthesis P))) _ ?_ ?_
    · exact bareVacuumHaar_congr (pmul_congr hF hF)
    · exact Q'.eqv_symm
        (bareVacuumHaar_congr (characterPow_two_product (synthesis P)))

theorem canonicalUsed_two_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 2 ≈
      bareVacuumHaar (characterPow (synthesis P) 2) := by
  exact Q'.eqv_trans _
    (trivalentVertexCartesianSum
      (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
      (vacuumPacket (linkAuxiliaryCutoff K))) _
    (canonicalUsed_two_eq_trivalent P)
    (Q'.eqv_trans _
      (trivalentExplicitCartesianSum
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
        (vacuumPacket (linkAuxiliaryCutoff K))) _
      (trivalentVertexSum_eq_explicit _ _ _)
      (Q'.eqv_trans _
        (fusionHaar (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)) _
        (trivalentExplicit_vacuum_eq_fusionHaar _ _)
        (fusionHaar_facePacket_eq_degreeTwoHaar P)))

/-! ## 3. The canonical degree-three block -/

private theorem canonicalThree_packet_agrees {K : Nat}
    (P : CharacterPacket K) : ∀ edge, edge ∈ [0, 1, 2] →
    canonicalLinkGraphPacket P 3 edge =
      trivalentGraphPackets (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P) edge := by
  intro edge hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
  rcases hedge with rfl | rfl | rfl <;>
    simp [canonicalLinkGraphPacket, trivalentGraphPackets]

theorem canonicalUsed_three_eq_trivalent {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 3 ≈
      trivalentVertexCartesianSum
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P) := by
  have hpacket := vertexCartesianSum_packet_eq_on
    [0, 1, 2] [(0, 1, 2)]
    (canonicalLinkGraphPacket P 3)
    (trivalentGraphPackets
      (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
      (facePacketAtLinkCutoff P))
    (canonicalThree_packet_agrees P)
  exact Q'.eqv_of_eq (by
    change canonicalUsedVertexCartesianSum P 3 =
      vertexCartesianSum [0, 1, 2] [(0, 1, 2)]
        (trivalentGraphPackets
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
          (facePacketAtLinkCutoff P))
    exact hpacket)

private theorem trivalentTerm_eq_fusionFactor {L a b c : Nat}
    (A B C : CharacterPacket L) :
    trivalentCartesianTerm A B C a b c ≈
      (fusionInd a b c * (coeffAt A a * coeffAt B b)) * coeffAt C c := by
  unfold trivalentCartesianTerm fusionInd
  by_cases hfusion : fusionOK a b c = true
  · rw [if_pos hfusion, if_pos hfusion]
    refine Q'.eqv_trans _
      (coeffAt A a * (coeffAt B b * coeffAt C c)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))
    · refine Q'.eqv_trans _
        ((coeffAt A a * coeffAt B b) * coeffAt C c) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      exact qmul_congr
        (Q'.eqv_symm (Q'.one_mul_eqv _)) (Q'.eqv_refl _)
  · rw [if_neg hfusion, if_neg hfusion]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (0 * coeffAt C c) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.zero_mul_eqv _))

/-- Reorder the literal three-label graph sum and perform the first binary
fusion.  This is the finite-Fubini form needed by the degree-three block and
by the later long-chain induction. -/
theorem trivalentExplicit_eq_fusionDiagonal {L : Nat}
    (A B C : CharacterPacket L) :
    trivalentExplicitCartesianSum A B C ≈
      fsum (fun c => fusionCoeff A B c * coeffAt C c) (L + 1) := by
  unfold trivalentExplicitCartesianSum
  let factor : Nat → Nat → Nat → Q' := fun a b c =>
    (fusionInd a b c * (coeffAt A a * coeffAt B b)) * coeffAt C c
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun b => fsum (fun c => factor a b c)
      (L + 1)) (L + 1)) (L + 1)) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro a
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro b
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro c
    exact trivalentTerm_eq_fusionFactor A B C
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun c => fsum (fun b => factor a b c)
        (L + 1)) (L + 1)) (L + 1)) _ ?_ ?_
    · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro a
      exact YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun b c => factor a b c) (L + 1) (L + 1)
    · refine Q'.eqv_trans _
        (fsum (fun c => fsum (fun a => fsum (fun b => factor a b c)
          (L + 1)) (L + 1)) (L + 1)) _ ?_ ?_
      · exact YMGap.Continuum.CubeRatioBounds.fsum_swap
          (fun a c => fsum (fun b => factor a b c) (L + 1))
          (L + 1) (L + 1)
      · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro c
        change fsum (fun a => fsum (fun b =>
          (fusionInd a b c * (coeffAt A a * coeffAt B b)) *
            coeffAt C c) (L + 1)) (L + 1) ≈
          fusionCoeff A B c * coeffAt C c
        refine Q'.eqv_trans _
          (fsum (fun a =>
            fsum (fun b => fusionInd a b c *
              (coeffAt A a * coeffAt B b)) (L + 1) * coeffAt C c)
            (L + 1)) _ ?_ ?_
        · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          intro a
          exact Q'.eqv_symm
            (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
              (fun b => fusionInd a b c *
                (coeffAt A a * coeffAt B b))
              (coeffAt C c) (L + 1))
        · unfold fusionCoeff fusionProduct
          exact Q'.eqv_symm
            (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
              (fun a => fsum (fun b => fusionInd a b c *
                (coeffAt A a * coeffAt B b)) (L + 1))
              (coeffAt C c) (L + 1))

theorem trivalentExplicit_face_eq_truncatedFusionHaar {K : Nat}
    (P : CharacterPacket K) :
    trivalentExplicitCartesianSum
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P) ≈
      fusionHaar
        (truncatedFusionPacket
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P))
        (facePacketAtLinkCutoff P) := by
  let F := facePacketAtLinkCutoff P
  let T := truncatedFusionPacket F F
  refine Q'.eqv_trans _
    (fsum (fun c => fusionCoeff F F c * coeffAt F c)
      (linkAuxiliaryCutoff K + 1)) _
    (trivalentExplicit_eq_fusionDiagonal F F F) ?_
  refine Q'.eqv_trans _
    (fsum (fun c => coeffAt T c * coeffAt F c)
      (linkAuxiliaryCutoff K + 1)) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
    intro c hc
    have hcoeff : coeffAt T c = fusionCoeff F F c := by
      rw [coeffAt_of_lt T hc]
      rfl
    rw [hcoeff]
    exact Q'.eqv_refl _
  · exact Q'.eqv_symm (fusionHaar_eq_diagonal T F)

theorem truncatedFusionFaceHaar_eq_degreeThreeHaar {K : Nat}
    (P : CharacterPacket K) :
    fusionHaar
        (truncatedFusionPacket
          (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P))
        (facePacketAtLinkCutoff P) ≈
      bareVacuumHaar (characterPow (synthesis P) 3) := by
  let F := facePacketAtLinkCutoff P
  let T := truncatedFusionPacket F F
  have hfit : K + K ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hT : synthesis T ≈ₚ pmul (synthesis F) (synthesis F) :=
    synthesis_truncatedFusionPacket F F
      (facePacketAtLinkCutoff_supported P)
      (facePacketAtLinkCutoff_supported P) hfit
  have hF : synthesis F ≈ₚ synthesis P :=
    synthesis_padPacket (externalCutoff_le_linkAuxiliaryCutoff K) P
  have hpoly : pmul (synthesis T) (synthesis F) ≈ₚ
      pmul (pmul (synthesis P) (synthesis P)) (synthesis P) :=
    pmul_congr (peqv_trans hT (pmul_congr hF hF)) hF
  have hcharacterRight : characterPow (synthesis P) 3 ≈ₚ
      pmul (synthesis P) (pmul (synthesis P) (synthesis P)) :=
    peqv_trans (characterPow_three_eq_tripleSynthesis P)
      (rightAssociated_synthesis P P P)
  have hleftCharacter :
      pmul (pmul (synthesis P) (synthesis P)) (synthesis P) ≈ₚ
        characterPow (synthesis P) 3 :=
    peqv_trans
      (pmul_assoc (synthesis P) (synthesis P) (synthesis P))
      (peqv_symm hcharacterRight)
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis T) (synthesis F))) _ ?_ ?_
  · exact Q'.eqv_symm (barePairing_eq_fusionHaar T F)
  · exact bareVacuumHaar_congr (peqv_trans hpoly hleftCharacter)

theorem canonicalUsed_three_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    canonicalUsedVertexCartesianSum P 3 ≈
      bareVacuumHaar (characterPow (synthesis P) 3) := by
  exact Q'.eqv_trans _
    (trivalentVertexCartesianSum
      (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
      (facePacketAtLinkCutoff P)) _
    (canonicalUsed_three_eq_trivalent P)
    (Q'.eqv_trans _
      (trivalentExplicitCartesianSum
        (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P)) _
      (trivalentVertexSum_eq_explicit _ _ _)
      (Q'.eqv_trans _
        (fusionHaar
          (truncatedFusionPacket
            (facePacketAtLinkCutoff P) (facePacketAtLinkCutoff P))
          (facePacketAtLinkCutoff P)) _
        (trivalentExplicit_face_eq_truncatedFusionHaar P)
        (truncatedFusionFaceHaar_eq_degreeThreeHaar P)))

end YMGap.Continuum.Z4CanonicalTrivalentGraphHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.trivalentVertexSum_eq_explicit
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.canonicalUsed_two_eq_trivalent
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.trivalentExplicit_vacuum_eq_fusionHaar
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.fusionHaar_facePacket_eq_degreeTwoHaar
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.canonicalUsed_two_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.canonicalUsed_three_eq_trivalent
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.trivalentExplicit_eq_fusionDiagonal
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.trivalentExplicit_face_eq_truncatedFusionHaar
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.truncatedFusionFaceHaar_eq_degreeThreeHaar
#print axioms YMGap.Continuum.Z4CanonicalTrivalentGraphHaar.canonicalUsed_three_eq_bareHaar
