/-
# Left-associated link fusion for the production fuseChain resolver

The production `fuseChain` resolver combines the first two physical legs and
then feeds each new leg into the accumulated intermediate channel.  This is
left-associated.  `sequentialLinkPacket`, by contrast, is written with the
new external packet on the left of the previously accumulated packet.

For identical external face packets the two presentations synthesize to the
same character power, but they are not definitionally the same recursion.
This module constructs the left-associated packet that the graph syntax can
match directly.  Its support remains inside `degree*K`; through degree six
every truncation is lossless, its synthesis is the exact character power,
and its vacuum coefficient equals both the bare Haar moment and the existing
canonical sequential channel sum.

Honest scope: this supplies the correct recursive packet target for the
degree-at-least-two `fuseChain` Fubini proof.  The graph rewrite and actual
identifier transport remain separate successor obligations.
-/

import YMGap.Continuum.Z4SequentialGraphKernelBaseCases

namespace YMGap.Continuum.Z4LeftAssociatedLinkFusion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

/-- Packet recursion matching the left-associated production resolver. -/
def leftAssociatedLinkPacket {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K)
  | 0 => vacuumPacket (linkAuxiliaryCutoff K)
  | degree + 1 => truncatedFusionPacket
      (leftAssociatedLinkPacket P degree) (facePacketAtLinkCutoff P)

theorem leftAssociatedLinkPacket_supported {K : Nat}
    (P : CharacterPacket K) : ∀ degree,
    PacketSupportedThrough (leftAssociatedLinkPacket P degree) (degree * K)
  | 0 => by
      simpa using vacuumPacket_supported_zero (linkAuxiliaryCutoff K)
  | degree + 1 => by
      have h := truncatedFusionPacket_supported
        (leftAssociatedLinkPacket P degree) (facePacketAtLinkCutoff P)
        (leftAssociatedLinkPacket_supported P degree)
        (facePacketAtLinkCutoff_supported P)
      intro spin hspin
      apply h spin
      simpa [Nat.add_mul] using hspin

/-- Through degree six, the left-associated packet realizes the exact same
character power as the canonical sequential presentation. -/
theorem leftAssociatedLinkPacket_synthesis {K degree : Nat}
    (P : CharacterPacket K) (hdegree : degree ≤ linkIncidenceBound) :
    synthesis (leftAssociatedLinkPacket P degree) ≈ₚ
      characterPow (synthesis P) degree := by
  induction degree with
  | zero =>
      let zeroIndex : Fin (linkAuxiliaryCutoff K + 1) :=
        ⟨0, Nat.succ_pos _⟩
      have hvac : leftAssociatedLinkPacket P 0 = basisPacket zeroIndex := rfl
      rw [hvac]
      exact peqv_trans (synthesis_basis zeroIndex) (peqv_refl _)
  | succ d ih =>
      have hd : d ≤ linkIncidenceBound := by omega
      have hfit : d * K + K ≤ linkAuxiliaryCutoff K := by
        unfold linkAuxiliaryCutoff
        have hmul := Nat.mul_le_mul_right K hdegree
        simpa [Nat.add_mul] using hmul
      have hstep := synthesis_truncatedFusionPacket
        (leftAssociatedLinkPacket P d) (facePacketAtLinkCutoff P)
        (leftAssociatedLinkPacket_supported P d)
        (facePacketAtLinkCutoff_supported P) hfit
      have hface := synthesis_padPacket
        (externalCutoff_le_linkAuxiliaryCutoff K) P
      refine peqv_trans hstep ?_
      simp only [characterPow]
      refine peqv_trans (pmul_congr (ih hd) (by
        simpa [facePacketAtLinkCutoff] using hface)) ?_
      exact pmul_comm _ _

def leftAssociatedLinkChannelSum {K : Nat}
    (P : CharacterPacket K) (degree : Nat) : Q' :=
  vacuumHaar (leftAssociatedLinkPacket P degree)

theorem leftAssociatedLinkChannelSum_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    leftAssociatedLinkChannelSum P degree ≈
      bareVacuumHaar (characterPow (synthesis P) degree) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (leftAssociatedLinkPacket P degree))) _
    (Q'.eqv_symm
      (bareVacuumHaar_synthesis_packet
        (leftAssociatedLinkPacket P degree))) ?_
  exact bareVacuumHaar_congr
    (leftAssociatedLinkPacket_synthesis P hdegree)

theorem leftAssociatedLinkChannelSum_eq_canonical
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    leftAssociatedLinkChannelSum P degree ≈
      canonicalSequentialLinkChannelSum P degree := by
  exact Q'.eqv_trans _
    (bareVacuumHaar (characterPow (synthesis P) degree)) _
    (leftAssociatedLinkChannelSum_eq_bareHaar P hdegree)
    (Q'.eqv_symm
      (canonicalSequentialLinkChannelSum_eq_bareHaar P hdegree))

end YMGap.Continuum.Z4LeftAssociatedLinkFusion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LeftAssociatedLinkFusion.leftAssociatedLinkPacket_supported
#print axioms YMGap.Continuum.Z4LeftAssociatedLinkFusion.leftAssociatedLinkPacket_synthesis
#print axioms YMGap.Continuum.Z4LeftAssociatedLinkFusion.leftAssociatedLinkChannelSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4LeftAssociatedLinkFusion.leftAssociatedLinkChannelSum_eq_canonical
