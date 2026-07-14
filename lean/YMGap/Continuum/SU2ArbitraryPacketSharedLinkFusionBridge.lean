/-
# Arbitrary-cutoff packets feed the shared-link fusion carrier

Two plaquettes carrying finite SU(2) character packets meet on a shared link
by Clebsch--Gordan multiplication.  The existing `fusionPacket` implements
that multiplication at one cutoff.  Here we prove that it is coherent with
every zero-padding map: fusing after increasing the cutoff gives the same
zero-extended coefficient sequence as fusing first and padding the result.

Consequently the construction defines one honest shared-link state in the
packet colimit and its constructive GNS completion.  Its dense Gram is the
existing interacting Wilson/Haar state and the completed physical transfer
acts by transferring the fused packet, not by independently transferring the
two plaquette factors.

Honest scope: this is one shared link between two arbitrary finite class
packets.  It does not impose the simultaneous vertex quotients of a full
four-dimensional lattice.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
import YMGap.Continuum.SU2CharacterFusionSynthesis

namespace YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_zero_extension {f : Nat → Q'} {n m : Nat}
    (hnm : n ≤ m) (hz : ∀ i, n ≤ i → f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (q_add_zero_eqv _)

/-! ## Cutoff coherence of Clebsch--Gordan fusion -/

/-- Increasing a common input cutoff adds only zero rows and columns to the
Clebsch--Gordan double sum. -/
theorem fusionCoeff_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) (s : Nat) :
    fusionCoeff (padPacket hNM P) (padPacket hNM Q) s ≈
      fusionCoeff P Q s := by
  unfold fusionCoeff fusionProduct
  let term := fun a b =>
    fusionInd a b s * (coeffAt P a * coeffAt Q b)
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun b => term a b) (M + 1)) (M + 1)) _ ?_ ?_
  · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
      YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun b => by
        simp only [term, coeffAt_padPacket]
        exact Q'.eqv_refl _) (M + 1)) (M + 1)
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun b => term a b) (N + 1)) (M + 1)) _ ?_ ?_
    · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
        fsum_zero_extension (by omega) (fun b hb => by
          have hQ : coeffAt Q b = 0 := coeffAt_of_gt Q (by omega)
          simp only [term, hQ]
          exact Q'.eqv_trans _ (fusionInd a b s * 0) _
            (Q'.mul_eqv_congr_left _ _ _ (q_mul_zero (coeffAt P a)))
            (Q'.mul_zero_eqv _))) (M + 1)
    · exact fsum_zero_extension (by omega) (fun a ha => by
        have hP : coeffAt P a = 0 := coeffAt_of_gt P (by omega)
        apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
        intro b hb
        simp only [term, hP]
        exact Q'.eqv_trans _ (fusionInd a b s * 0) _
          (Q'.mul_eqv_congr_left _ _ _ (q_zero_mul (coeffAt Q b)))
          (Q'.mul_zero_eqv _))

private theorem fusionCoeff_zero_above {N : Nat}
    (P Q : CharacterPacket N) (s : Nat) (hs : 2 * N < s) :
    fusionCoeff P Q s ≈ 0 := by
  unfold fusionCoeff fusionProduct
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro a ha
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro b hb
  have hab : a + b < s := by omega
  have hind : fusionInd a b s = 0 := by
    unfold fusionInd fusionOK
    simp [show ¬ s ≤ a + b by omega]
  rw [hind]
  exact q_zero_mul _

/-- The two-plaquette shared-link quotient commutes with every directed
cutoff inclusion. -/
theorem fusionPacket_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    PacketEqv
      (fusionPacket (padPacket hNM P) (padPacket hNM Q))
      (padPacket (Nat.mul_le_mul_left 2 hNM) (fusionPacket P Q)) := by
  intro i
  change fusionCoeff (padPacket hNM P) (padPacket hNM Q) i.val ≈
    coeffAt (fusionPacket P Q) i.val
  refine Q'.eqv_trans _ (fusionCoeff P Q i.val) _
    (fusionCoeff_pad hNM P Q i.val) ?_
  by_cases hi : i.val < 2 * N + 1
  · rw [coeffAt_of_lt (fusionPacket P Q) hi]
    exact Q'.eqv_refl _
  · rw [coeffAt_of_gt (fusionPacket P Q) (by omega)]
    exact fusionCoeff_zero_above P Q i.val (by omega)

/-! ## One concrete arbitrary-cutoff shared-link state -/

/-- The fused two-plaquette state at its exact output cutoff. -/
def sharedLinkStage {N : Nat} (P Q : CharacterPacket N) : StagedPacket :=
  stagePacket (fusionPacket P Q)

/-- Its canonical vector in the constructive packet-colimit completion. -/
def completedSharedLinkState {N : Nat} (P Q : CharacterPacket N) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS (sharedLinkStage P Q)

private theorem embedV_eq_of_veq (D : GNSData) {a b : D.V}
    (h : D.veq a b) : embedV D a = embedV D b := by
  apply Quotient.sound
  exact embed_null_of_rad D (rad_of_veq D h)

/-- Padding either plaquette carrier before fusing gives literally the same
vector after passage to the completed colimit. -/
theorem completedSharedLinkState_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    completedSharedLinkState (padPacket hNM P) (padPacket hNM Q) =
      completedSharedLinkState P Q := by
  unfold completedSharedLinkState sharedLinkStage
  apply embedV_eq_of_veq packetColimitGNS
  intro s
  refine Q'.eqv_trans _
    (coeffAt
      (padPacket (Nat.mul_le_mul_left 2 hNM) (fusionPacket P Q)) s) _ ?_ ?_
  · exact coeffAt_packetEqv (fusionPacket_pad hNM P Q) s
  · rw [coeffAt_padPacket]
    exact Q'.eqv_refl _

/-- On two fused shared-link states, the colimit GNS form is exactly the
existing interacting Wilson/Haar Gram of the Clebsch--Gordan packets. -/
theorem sharedLinkStage_gram {N : Nat}
    (P Q : CharacterPacket N) :
    packetColimitGNS.B (sharedLinkStage P Q) (sharedLinkStage P Q) ≈
      packetWilsonGram (fusionPacket P Q) (fusionPacket P Q) :=
  stagedGram_self_eq_packet (sharedLinkStage P Q)

/-- The shared-link Gram is the literal bare Haar functional on the two
synthesized fused plaquette products, with one physical link transfer
inserted. -/
theorem sharedLinkStage_same_state {N : Nat}
    (P Q : CharacterPacket N) :
    packetColimitGNS.B (sharedLinkStage P Q) (sharedLinkStage P Q) ≈
      bareVacuumHaar
        (pmul
          (synthesis (packetTransfer (fusionPacket P Q)))
          (synthesis (fusionPacket P Q))) := by
  refine Q'.eqv_trans _
    (packetWilsonGram (fusionPacket P Q) (fusionPacket P Q)) _
    (sharedLinkStage_gram P Q) ?_
  exact Q'.eqv_symm
    (barePolynomial_same_state_identification
      (fusionPacket P Q) (fusionPacket P Q))

/-- The completed physical one-link transfer is no longer isolated: on every
finite two-plaquette shared-link state it acts on the fused packet itself. -/
theorem completedSharedLinkState_transfer {N : Nat}
    (P Q : CharacterPacket N) :
    completedPacketTransfer (completedSharedLinkState P Q) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer (fusionPacket P Q))) := by
  exact completedPacketTransfer_embed (sharedLinkStage P Q)

/-! ## Two inputs with genuinely different cutoffs -/

/-- Canonical common cutoff for two independently truncated plaquette
packets. -/
def sharedCutoff (N M : Nat) : Nat := Nat.max N M

def padSharedLeft {N M : Nat} (P : CharacterPacket N) :
    CharacterPacket (sharedCutoff N M) :=
  padPacket (Nat.le_max_left N M) P

def padSharedRight {N M : Nat} (Q : CharacterPacket M) :
    CharacterPacket (sharedCutoff N M) :=
  padPacket (Nat.le_max_right N M) Q

/-- Clebsch--Gordan carrier of two plaquettes whose original cutoffs need not
agree. -/
def arbitrarySharedLinkPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    CharacterPacket (2 * sharedCutoff N M) :=
  fusionPacket (padSharedLeft (M := M) P) (padSharedRight (N := N) Q)

def arbitrarySharedLinkStage {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : StagedPacket :=
  stagePacket (arbitrarySharedLinkPacket P Q)

def completedArbitrarySharedLinkState {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS (arbitrarySharedLinkStage P Q)

/-- The unequal-cutoff carrier still synthesizes to the literal pointwise
product of the two padded plaquette character sums. -/
theorem arbitrarySharedLink_synthesis {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PolyEqv (synthesis (arbitrarySharedLinkPacket P Q))
      (pmul (synthesis (padSharedLeft (M := M) P))
        (synthesis (padSharedRight (N := N) Q))) :=
  synthesis_fusionPacket_product _ _

/-- Exact shared-link Haar normalization: the vacuum channel is the diagonal
over the two zero-extended input sequences, at the canonical common cutoff. -/
theorem arbitrarySharedLink_vacuum_diagonal {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    vacuumHaar (arbitrarySharedLinkPacket P Q) ≈
      fsum (fun s => coeffAt P s * coeffAt Q s)
        (sharedCutoff N M + 1) := by
  refine Q'.eqv_trans _
    (fusionHaar (padSharedLeft (M := M) P)
      (padSharedRight (N := N) Q)) _
    (vacuumHaar_fusionPacket _ _) ?_
  refine Q'.eqv_trans _
    (fsum (fun s =>
      coeffAt (padSharedLeft (M := M) P) s *
        coeffAt (padSharedRight (N := N) Q) s)
      (sharedCutoff N M + 1)) _
    (fusionHaar_eq_diagonal _ _) ?_
  exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun s => by
    simp only [padSharedLeft, padSharedRight, coeffAt_padPacket]
    exact Q'.eqv_refl _) (sharedCutoff N M + 1)

/-- Exact interacting norm of the genuinely unequal-cutoff fused state. -/
theorem arbitrarySharedLinkStage_gram {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    packetColimitGNS.B (arbitrarySharedLinkStage P Q)
        (arbitrarySharedLinkStage P Q) ≈
      packetWilsonGram (arbitrarySharedLinkPacket P Q)
        (arbitrarySharedLinkPacket P Q) :=
  stagedGram_self_eq_packet (arbitrarySharedLinkStage P Q)

/-- The physical completed transfer acts after the two plaquette packets have
been fused at their shared link. -/
theorem completedArbitrarySharedLinkState_transfer {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedPacketTransfer (completedArbitrarySharedLinkState P Q) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer (arbitrarySharedLinkPacket P Q))) := by
  exact completedPacketTransfer_embed (arbitrarySharedLinkStage P Q)

end YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge

#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.fusionCoeff_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.fusionPacket_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.completedSharedLinkState_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.sharedLinkStage_gram
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.sharedLinkStage_same_state
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.completedSharedLinkState_transfer
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.arbitrarySharedLink_synthesis
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.arbitrarySharedLink_vacuum_diagonal
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.arbitrarySharedLinkStage_gram
#print axioms YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge.completedArbitrarySharedLinkState_transfer
