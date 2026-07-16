/-
# Canonical sequential link fusion equals the local Haar moment

The finite-box resolver `fuseLabels` uses a left-to-right fusion chain.  This
module realizes that same channel mechanism at the coefficient level inside
the conservative cutoff `6*K`.

A truncated fusion packet keeps output channels only through `6*K`.  A
support theorem proves that fusing packets supported through `A` and `B`
produces nothing above `A+B`.  Therefore each truncation in a chain of at most
six cutoff-`K` face packets is lossless.  Exact character synthesis then shows
that the sequential packet after `d` legs represents the `d`-th character
power.  Its vacuum coefficient is consequently the bare Haar moment.

This closes the canonical local fusion mechanism for every actual finite-box
link.  It still does not multiply overlapping link identities into a global
box integral; that requires a separate finite Fubini/edge-sharing theorem.
-/

import YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar

namespace YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Support arithmetic for an exact truncated fusion -/

/-- A packet has no coefficient above the supplied support bound. -/
def PacketSupportedThrough {L : Nat} (P : CharacterPacket L)
    (bound : Nat) : Prop :=
  ∀ spin, bound < spin → coeffAt P spin ≈ 0

/-- Output packet of one Clebsch--Gordan product, retained at the same ambient
cutoff. -/
def truncatedFusionPacket {L : Nat}
    (A B : CharacterPacket L) : CharacterPacket L where
  coeff i := fusionCoeff A B i.val

theorem fusionInd_zero_of_add_lt {a b s : Nat} (h : a + b < s) :
    fusionInd a b s = 0 := by
  unfold fusionInd
  rw [if_neg]
  intro hfusion
  have hout := fusionOK_output_le_add hfusion
  omega

/-- Exact support addition for Clebsch--Gordan coefficients. -/
theorem fusionCoeff_zero_above_support {L aBound bBound : Nat}
    (A B : CharacterPacket L)
    (hA : PacketSupportedThrough A aBound)
    (hB : PacketSupportedThrough B bBound)
    {s : Nat} (hs : aBound + bBound < s) :
    fusionCoeff A B s ≈ 0 := by
  unfold fusionCoeff fusionProduct
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro a ha
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro b hb
  by_cases habound : a ≤ aBound
  · by_cases hbbound : b ≤ bBound
    · rw [fusionInd_zero_of_add_lt (a := a) (b := b) (s := s) (by omega)]
      exact Q'.zero_mul_eqv _
    · have hbzero := hB b (by omega)
      refine Q'.eqv_trans _
        (fusionInd a b s * (coeffAt A a * 0)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hbzero)
      · exact Q'.eqv_trans _ (fusionInd a b s * 0) _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
          (Q'.mul_zero_eqv _)
  · have hazero := hA a (by omega)
    refine Q'.eqv_trans _
      (fusionInd a b s * (0 * coeffAt B b)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hazero)
    · exact Q'.eqv_trans _ (fusionInd a b s * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
        (Q'.mul_zero_eqv _)

theorem truncatedFusionPacket_supported {L aBound bBound : Nat}
    (A B : CharacterPacket L)
    (hA : PacketSupportedThrough A aBound)
    (hB : PacketSupportedThrough B bBound) :
    PacketSupportedThrough (truncatedFusionPacket A B)
      (aBound + bBound) := by
  intro spin hspin
  by_cases hL : spin < L + 1
  · rw [coeffAt_of_lt _ hL]
    exact fusionCoeff_zero_above_support A B hA hB hspin
  · rw [coeffAt_of_gt _ (by omega)]
    exact Q'.eqv_refl 0

/-! ## 2. Lossless truncation and synthesis -/

theorem synthesis_congr_of_packetEqv {N : Nat}
    {A B : CharacterPacket N} (hAB : PacketEqv A B) :
    synthesis A ≈ₚ synthesis B := by
  intro x
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt A s * Cheb.U s x) (N + 1)) _
    (eval_synthesis A x) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt B s * Cheb.U s x) (N + 1)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_right _ _ _ (coeffAt_packetEqv hAB s)) (N + 1)
  · exact Q'.eqv_symm (eval_synthesis B x)

/-- If the true output support fits inside `L`, retaining only cutoff `L`
loses no character coefficient. -/
theorem fullFusion_eqv_paddedTruncation
    {L aBound bBound : Nat} (A B : CharacterPacket L)
    (hA : PacketSupportedThrough A aBound)
    (hB : PacketSupportedThrough B bBound)
    (hfit : aBound + bBound ≤ L) :
    PacketEqv (fusionPacket A B)
      (padPacket (show L ≤ 2 * L by omega)
        (truncatedFusionPacket A B)) := by
  intro i
  change fusionCoeff A B i.val ≈
    coeffAt (truncatedFusionPacket A B) i.val
  by_cases hi : i.val < L + 1
  · rw [coeffAt_of_lt _ hi]
    exact Q'.eqv_refl _
  · rw [coeffAt_of_gt _ (by omega)]
    exact fusionCoeff_zero_above_support A B hA hB (by omega)

/-- Lossless truncated fusion synthesizes to literal polynomial
multiplication. -/
theorem synthesis_truncatedFusionPacket {L aBound bBound : Nat}
    (A B : CharacterPacket L)
    (hA : PacketSupportedThrough A aBound)
    (hB : PacketSupportedThrough B bBound)
    (hfit : aBound + bBound ≤ L) :
    synthesis (truncatedFusionPacket A B) ≈ₚ
      pmul (synthesis A) (synthesis B) := by
  let hL : L ≤ 2 * L := by omega
  let T := truncatedFusionPacket A B
  have hpacket : PacketEqv (fusionPacket A B) (padPacket hL T) :=
    fullFusion_eqv_paddedTruncation A B hA hB hfit
  refine peqv_trans
    (peqv_symm (synthesis_padPacket hL T)) ?_
  refine peqv_trans
    (peqv_symm (synthesis_congr_of_packetEqv hpacket)) ?_
  exact synthesis_fusionPacket_product A B

/-! ## 3. The canonical sequential packet -/

def facePacketAtLinkCutoff {K : Nat} (P : CharacterPacket K) :
    CharacterPacket (linkAuxiliaryCutoff K) :=
  padPacket (externalCutoff_le_linkAuxiliaryCutoff K) P

def sequentialLinkPacket {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K)
  | 0 => vacuumPacket (linkAuxiliaryCutoff K)
  | d + 1 => truncatedFusionPacket
      (facePacketAtLinkCutoff P) (sequentialLinkPacket P d)

theorem facePacketAtLinkCutoff_supported {K : Nat}
    (P : CharacterPacket K) :
    PacketSupportedThrough (facePacketAtLinkCutoff P) K := by
  intro spin hspin
  unfold facePacketAtLinkCutoff
  rw [coeffAt_padPacket, coeffAt_of_gt _ hspin]
  exact Q'.eqv_refl 0

theorem vacuumPacket_supported_zero (L : Nat) :
    PacketSupportedThrough (vacuumPacket L) 0 := by
  intro spin hspin
  rw [YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
  rw [if_neg (by omega)]
  exact Q'.eqv_refl 0

/-- After `d` legs, the sequential packet is supported through `d*K`. -/
theorem sequentialLinkPacket_supported {K : Nat}
    (P : CharacterPacket K) : ∀ d : Nat,
    PacketSupportedThrough (sequentialLinkPacket P d) (d * K)
  | 0 => by
      simpa using vacuumPacket_supported_zero (linkAuxiliaryCutoff K)
  | d + 1 => by
      have h := truncatedFusionPacket_supported
        (facePacketAtLinkCutoff P) (sequentialLinkPacket P d)
        (facePacketAtLinkCutoff_supported P)
        (sequentialLinkPacket_supported P d)
      intro spin hspin
      apply h spin
      simpa [Nat.add_mul, Nat.add_comm] using hspin

/-- Through degree six, the sequential chain synthesizes to the exact
character power. -/
theorem sequentialLinkPacket_synthesis {K degree : Nat}
    (P : CharacterPacket K) (hdegree : degree ≤ linkIncidenceBound) :
    synthesis (sequentialLinkPacket P degree) ≈ₚ
      characterPow (synthesis P) degree := by
  induction degree with
  | zero =>
      let zeroIndex : Fin (linkAuxiliaryCutoff K + 1) :=
        ⟨0, Nat.succ_pos _⟩
      have hvac : vacuumPacket (linkAuxiliaryCutoff K) =
          basisPacket zeroIndex := rfl
      rw [sequentialLinkPacket, hvac]
      exact peqv_trans (synthesis_basis zeroIndex) (peqv_refl _)
  | succ d ih =>
      have hd : d ≤ linkIncidenceBound := by omega
      have hfit : K + d * K ≤ linkAuxiliaryCutoff K := by
        unfold linkAuxiliaryCutoff
        have hmul := Nat.mul_le_mul_right K hdegree
        simpa [Nat.add_mul, Nat.add_comm] using hmul
      have hstep := synthesis_truncatedFusionPacket
        (facePacketAtLinkCutoff P) (sequentialLinkPacket P d)
        (facePacketAtLinkCutoff_supported P)
        (sequentialLinkPacket_supported P d) hfit
      refine peqv_trans hstep ?_
      have hface := synthesis_padPacket
        (externalCutoff_le_linkAuxiliaryCutoff K) P
      simpa only [characterPow] using
        (pmul_congr hface (ih hd))

/-- Vacuum coefficient of the canonical sequential link fusion. -/
def canonicalSequentialLinkChannelSum {K : Nat}
    (P : CharacterPacket K) (degree : Nat) : Q' :=
  vacuumHaar (sequentialLinkPacket P degree)

/-- **Canonical sequential local Haar completeness.** -/
theorem canonicalSequentialLinkChannelSum_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    canonicalSequentialLinkChannelSum P degree ≈
      bareVacuumHaar (characterPow (synthesis P) degree) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (sequentialLinkPacket P degree))) _ ?_ ?_
  · exact Q'.eqv_symm
      (bareVacuumHaar_synthesis_packet (sequentialLinkPacket P degree))
  · exact bareVacuumHaar_congr
      (sequentialLinkPacket_synthesis P hdegree)

/-! ## 4. Every actual finite-box link -/

def actualCanonicalLinkChannelSum (K n : Nat)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Q' :=
  canonicalSequentialLinkChannelSum (heatKernelPacket K coupling)
    (incidentPlaqIds n ell).length

/-- The actual canonical sequential channel sum at every box link is the
same local Haar moment already identified by the balanced presentation. -/
theorem actualCanonicalLinkChannelSum_eq_bareHaar
    (K n : Nat) (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    actualCanonicalLinkChannelSum K n ell ≈
      actualLinkBareHaarMoment K n ell := by
  exact canonicalSequentialLinkChannelSum_eq_bareHaar
    (heatKernelPacket K coupling)
    (incidentPlaqIds_length_le_six n ell)

theorem actualCanonicalLinkChannelSum_eq_balanced
    (K n : Nat) (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    actualCanonicalLinkChannelSum K n ell ≈
      actualLinkCompleteChannelSum K n ell := by
  exact Q'.eqv_trans _ (actualLinkBareHaarMoment K n ell) _
    (actualCanonicalLinkChannelSum_eq_bareHaar K n ell)
    (Q'.eqv_symm (actualLinkCompleteChannelSum_eq_bareHaar K n ell))

end YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.fusionInd_zero_of_add_lt
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.fusionCoeff_zero_above_support
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.truncatedFusionPacket_supported
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.synthesis_congr_of_packetEqv
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.fullFusion_eqv_paddedTruncation
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.synthesis_truncatedFusionPacket
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.sequentialLinkPacket_supported
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.sequentialLinkPacket_synthesis
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.canonicalSequentialLinkChannelSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.actualCanonicalLinkChannelSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar.actualCanonicalLinkChannelSum_eq_balanced
