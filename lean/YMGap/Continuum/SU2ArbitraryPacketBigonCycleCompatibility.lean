/-
# Arbitrary finite character packets on the two-link bigon

The one-shared-link fusion carrier becomes a first genuine cycle when the
same two plaquette packets meet on two oppositely oriented links.  The forward
link carries `P * Q`; the reverse link carries `Q * P`.  This file packages
both links together, proves that their orientation closure is exact, and
checks cutoff, synthesis, Gram, and transfer compatibility simultaneously.

The inputs may have different finite cutoffs: both are zero-extended to their
canonical maximum before either link is fused.  Thus no coefficient is chosen
or measured, and no fixed truncation is built into the construction.

Honest scope: the bigon is the minimal bivalent cycle.  The result does not yet
construct arbitrary-valence vertex intertwiners, impose simultaneous quotients
on a general four-dimensional lattice, or control the thermodynamic limit.
-/

import YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge

namespace YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility

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
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd fusionOK
  simp only [Nat.max_comm, Nat.min_comm, Nat.add_comm]

/-- Clebsch--Gordan fusion is commutative coefficientwise for arbitrary
finite packets, not only after applying the vacuum functional. -/
theorem fusionCoeff_comm {N : Nat} (P Q : CharacterPacket N) (s : Nat) :
    fusionCoeff P Q s ≈ fusionCoeff Q P s := by
  unfold fusionCoeff fusionProduct
  refine Q'.eqv_trans _
    (fsum (fun b => fsum (fun a =>
      fusionInd a b s * (coeffAt P a * coeffAt Q b)) (N + 1)) (N + 1)) _
    (YMGap.Continuum.CubeRatioBounds.fsum_swap
      (fun a b => fusionInd a b s * (coeffAt P a * coeffAt Q b))
      (N + 1) (N + 1)) ?_
  exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun b =>
    YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a => by
      rw [fusionInd_comm a b s]
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv (coeffAt P a) (coeffAt Q b))) (N + 1)) (N + 1)

/-- Packet-level orientation reversal for a shared link. -/
theorem fusionPacket_comm {N : Nat} (P Q : CharacterPacket N) :
    PacketEqv (fusionPacket P Q) (fusionPacket Q P) := by
  intro i
  exact fusionCoeff_comm P Q i.val

private theorem packetEqv_trans {N : Nat} {P Q R : CharacterPacket N}
    (hPQ : PacketEqv P Q) (hQR : PacketEqv Q R) : PacketEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

/-- Fusion respects coefficient setoid equality in both inputs. -/
theorem fusionPacket_congr {N : Nat} {P P' Q Q₂ : CharacterPacket N}
    (hP : PacketEqv P P') (hQ : PacketEqv Q Q₂) :
    PacketEqv (fusionPacket P Q) (fusionPacket P' Q₂) := by
  intro i
  unfold fusionPacket fusionCoeff fusionProduct
  exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
    YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun b =>
      Q'.mul_eqv_congr_left (fusionInd a b i.val) _ _
        (q_mul_congr (coeffAt_packetEqv hP a)
          (coeffAt_packetEqv hQ b))) (N + 1)) (N + 1)

private theorem packetTransfer_congr {N : Nat} {P Q : CharacterPacket N}
    (h : PacketEqv P Q) : PacketEqv (packetTransfer P) (packetTransfer Q) := by
  intro i
  exact Q'.mul_eqv_congr_left (packetEigen i.val) _ _ (h i)

/-! ## The simultaneous two-link carrier -/

/-- A bigon has two oppositely oriented copies of the same shared boundary. -/
abbrev BigonPacket (K : Nat) :=
  CharacterPacket (2 * K) × CharacterPacket (2 * K)

def BigonEqv {K : Nat} (X Y : BigonPacket K) : Prop :=
  PacketEqv X.1 Y.1 ∧ PacketEqv X.2 Y.2

/-- Forward and reverse fusion are formed at one cutoff and retained as one
cycle carrier. -/
def bigonPacket {K : Nat} (P Q : CharacterPacket K) : BigonPacket K :=
  (fusionPacket P Q, fusionPacket Q P)

/-- Independently truncated plaquettes are first embedded at their canonical
common cutoff, then used on both oriented links of the bigon. -/
def arbitraryBigonPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    BigonPacket (sharedCutoff N M) :=
  bigonPacket (padSharedLeft (M := M) P) (padSharedRight (N := N) Q)

/-- The two orientations close simultaneously in the coefficient quotient. -/
theorem arbitraryBigon_orientation_closure {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PacketEqv (arbitraryBigonPacket P Q).1
      (arbitraryBigonPacket P Q).2 :=
  fusionPacket_comm _ _

/-- Padding both plaquette inputs pads both links of the bigon in one coherent
directed-system square. -/
theorem bigonPacket_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    BigonEqv (bigonPacket (padPacket hNM P) (padPacket hNM Q))
      (padPacket (Nat.mul_le_mul_left 2 hNM) (bigonPacket P Q).1,
        padPacket (Nat.mul_le_mul_left 2 hNM) (bigonPacket P Q).2) := by
  exact ⟨fusionPacket_pad hNM P Q, fusionPacket_pad hNM Q P⟩

/-- The canonical common cutoff is monotone under two independent input
cutoff enlargements. -/
private theorem sharedCutoff_mono {N N' M M' : Nat}
    (hNN : N ≤ N') (hMM : M ≤ M') :
    sharedCutoff N M ≤ sharedCutoff N' M' := by
  apply (Nat.max_le).2
  exact ⟨Nat.le_trans hNN (Nat.le_max_left _ _),
    Nat.le_trans hMM (Nat.le_max_right _ _)⟩

/-- **Independent-cutoff coherence for the whole bigon.**  Enlarging the two
input truncations by unrelated amounts and then constructing the cycle agrees
with constructing it first and padding both oriented fused links. -/
theorem arbitraryBigonPacket_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    BigonEqv
      (arbitraryBigonPacket (padPacket hNN P) (padPacket hMM Q))
      (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono hNN hMM))
          (arbitraryBigonPacket P Q).1,
        padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono hNN hMM))
          (arbitraryBigonPacket P Q).2) := by
  let K := sharedCutoff N M
  let K' := sharedCutoff N' M'
  have hKK : K ≤ K' := sharedCutoff_mono hNN hMM
  let A : CharacterPacket K := padSharedLeft (M := M) P
  let B : CharacterPacket K := padSharedRight (N := N) Q
  let A' : CharacterPacket K' :=
    padSharedLeft (M := M') (padPacket hNN P)
  let B' : CharacterPacket K' :=
    padSharedRight (N := N') (padPacket hMM Q)
  have hA : PacketEqv A' (padPacket hKK A) := by
    intro i
    change coeffAt (padPacket hNN P) i.val ≈ coeffAt A i.val
    simp only [A, padSharedLeft, coeffAt_padPacket]
    exact Q'.eqv_refl _
  have hB : PacketEqv B' (padPacket hKK B) := by
    intro i
    change coeffAt (padPacket hMM Q) i.val ≈ coeffAt B i.val
    simp only [B, padSharedRight, coeffAt_padPacket]
    exact Q'.eqv_refl _
  change BigonEqv (fusionPacket A' B', fusionPacket B' A')
    (padPacket (Nat.mul_le_mul_left 2 hKK) (fusionPacket A B),
      padPacket (Nat.mul_le_mul_left 2 hKK) (fusionPacket B A))
  exact ⟨
    packetEqv_trans (fusionPacket_congr hA hB) (fusionPacket_pad hKK A B),
    packetEqv_trans (fusionPacket_congr hB hA) (fusionPacket_pad hKK B A)⟩

/-! ## Exact synthesis and Gram compatibility around the cycle -/

/-- Both oriented link polynomials and their common unoriented product are
identified in one theorem. -/
theorem arbitraryBigon_synthesis_cycle {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PolyEqv (synthesis (arbitraryBigonPacket P Q).1)
        (pmul (synthesis (padSharedLeft (M := M) P))
          (synthesis (padSharedRight (N := N) Q))) ∧
    PolyEqv (synthesis (arbitraryBigonPacket P Q).2)
        (pmul (synthesis (padSharedRight (N := N) Q))
          (synthesis (padSharedLeft (M := M) P))) ∧
    PolyEqv (synthesis (arbitraryBigonPacket P Q).1)
      (synthesis (arbitraryBigonPacket P Q).2) := by
  refine ⟨synthesis_fusionPacket_product _ _,
    synthesis_fusionPacket_product _ _, ?_⟩
  exact peqv_trans (synthesis_fusionPacket_product _ _)
    (peqv_trans (pmul_comm _ _)
      (peqv_symm (synthesis_fusionPacket_product _ _)))

/-- The interacting cycle Gram pairs the forward and reverse link carriers;
it is not a relabelled one-link self-norm definition. -/
def arbitraryBigonCycleGram {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : Q' :=
  packetWilsonGram (arbitraryBigonPacket P Q).1
    (arbitraryBigonPacket P Q).2

/-- Orientation closure turns the cross-link cycle Gram into the exact
forward-link norm. -/
theorem arbitraryBigonCycleGram_eq_forward {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    arbitraryBigonCycleGram P Q ≈
      packetWilsonGram (arbitraryBigonPacket P Q).1
        (arbitraryBigonPacket P Q).1 := by
  unfold arbitraryBigonCycleGram
  exact packetWilsonGram_congr (fun _ => Q'.eqv_refl _)
    (packetEqv_symm (arbitraryBigon_orientation_closure P Q))

/-- Simultaneous two-link Gram: the two orientations are both retained, so
the value is the product of the two exact interacting link norms. -/
def arbitraryBigonProductGram {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : Q' :=
  packetWilsonGram (arbitraryBigonPacket P Q).1
      (arbitraryBigonPacket P Q).1 *
    packetWilsonGram (arbitraryBigonPacket P Q).2
      (arbitraryBigonPacket P Q).2

def arbitraryBigonStage {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    StagedPacket × StagedPacket :=
  (stagePacket (arbitraryBigonPacket P Q).1,
    stagePacket (arbitraryBigonPacket P Q).2)

/-- The product of the two dense colimit Grams is exactly the packet-level
two-link Gram. -/
theorem arbitraryBigonStage_gram {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    packetColimitGNS.B (arbitraryBigonStage P Q).1
        (arbitraryBigonStage P Q).1 *
      packetColimitGNS.B (arbitraryBigonStage P Q).2
        (arbitraryBigonStage P Q).2 ≈
      arbitraryBigonProductGram P Q := by
  exact q_mul_congr
    (stagedGram_self_eq_packet (arbitraryBigonStage P Q).1)
    (stagedGram_self_eq_packet (arbitraryBigonStage P Q).2)

/-! ## Transfer and completed cutoff coherence -/

def completedBigonState {N : Nat} (P Q : CharacterPacket N) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (completedSharedLinkState P Q, completedSharedLinkState Q P)

/-- The simultaneous completed bigon state is independent of a common
finite cutoff enlargement. -/
theorem completedBigonState_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    completedBigonState (padPacket hNM P) (padPacket hNM Q) =
      completedBigonState P Q := by
  apply Prod.ext
  · exact completedSharedLinkState_pad hNM P Q
  · exact completedSharedLinkState_pad hNM Q P

def completedArbitraryBigonState {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (embedV packetColimitGNS (arbitraryBigonStage P Q).1,
    embedV packetColimitGNS (arbitraryBigonStage P Q).2)

private theorem embedV_eq_of_veq (D : GNSData) {a b : D.V}
    (h : D.veq a b) : embedV D a = embedV D b := by
  apply Quotient.sound
  exact embed_null_of_rad D (rad_of_veq D h)

/-- Independent enlargement of the two input cutoffs leaves the completed
two-link cycle vector literally unchanged. -/
theorem completedArbitraryBigonState_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedArbitraryBigonState (padPacket hNN P) (padPacket hMM Q) =
      completedArbitraryBigonState P Q := by
  have hbig := arbitraryBigonPacket_pad_independent hNN hMM P Q
  apply Prod.ext
  · apply embedV_eq_of_veq packetColimitGNS
    intro s
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono hNN hMM))
          (arbitraryBigonPacket P Q).1) s) _ ?_ ?_
    · exact coeffAt_packetEqv hbig.1 s
    · rw [coeffAt_padPacket]
      exact Q'.eqv_refl _
  · apply embedV_eq_of_veq packetColimitGNS
    intro s
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono hNN hMM))
          (arbitraryBigonPacket P Q).2) s) _ ?_ ?_
    · exact coeffAt_packetEqv hbig.2 s
    · rw [coeffAt_padPacket]
      exact Q'.eqv_refl _

def completedBigonTransfer
    (x : GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (completedPacketTransfer x.1, completedPacketTransfer x.2)

/-- The physical transfer acts on both links of the completed bigon at once. -/
theorem completedArbitraryBigonState_transfer {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedBigonTransfer (completedArbitraryBigonState P Q) =
      (embedV packetColimitGNS
          (stagePacket (packetTransfer (arbitraryBigonPacket P Q).1)),
        embedV packetColimitGNS
          (stagePacket (packetTransfer (arbitraryBigonPacket P Q).2))) := by
  apply Prod.ext
  · exact completedPacketTransfer_embed (arbitraryBigonStage P Q).1
  · exact completedPacketTransfer_embed (arbitraryBigonStage P Q).2

/-- Orientation closure survives simultaneous physical transfer on both
links, so transfer descends to the bigon cycle quotient. -/
theorem arbitraryBigon_transfer_orientation_closure {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PacketEqv (packetTransfer (arbitraryBigonPacket P Q).1)
      (packetTransfer (arbitraryBigonPacket P Q).2) :=
  packetTransfer_congr (arbitraryBigon_orientation_closure P Q)

/-- One bundled base-case certificate: both-link cutoff coherence, exact
orientation closure, and transfer descent hold together for every pair of
finite packets at a common cutoff. -/
theorem bigon_cycle_quotient_compatible {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    BigonEqv (bigonPacket (padPacket hNM P) (padPacket hNM Q))
      (padPacket (Nat.mul_le_mul_left 2 hNM) (bigonPacket P Q).1,
        padPacket (Nat.mul_le_mul_left 2 hNM) (bigonPacket P Q).2) ∧
    PacketEqv (bigonPacket P Q).1 (bigonPacket P Q).2 ∧
    PacketEqv (packetTransfer (bigonPacket P Q).1)
      (packetTransfer (bigonPacket P Q).2) := by
  exact ⟨bigonPacket_pad hNM P Q, fusionPacket_comm P Q,
    packetTransfer_congr (fusionPacket_comm P Q)⟩

end YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility

#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.fusionCoeff_comm
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.fusionPacket_comm
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.fusionPacket_congr
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigon_orientation_closure
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.bigonPacket_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigonPacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigon_synthesis_cycle
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigonCycleGram_eq_forward
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigonStage_gram
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.completedBigonState_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.completedArbitraryBigonState_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.completedArbitraryBigonState_transfer
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.arbitraryBigon_transfer_orientation_closure
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility.bigon_cycle_quotient_compatible
