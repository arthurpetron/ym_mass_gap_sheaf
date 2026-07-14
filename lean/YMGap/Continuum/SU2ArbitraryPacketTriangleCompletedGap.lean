/-
# Independent-cutoff and completed gap for the trivalent triangle

The concrete three-vertex triangle evaluator already keeps its three shared
labels and all three intertwiner constraints in one joint finite sum.  This
module first places nine independently truncated packet decorations at one
canonical common cutoff and proves that unrelated cutoff enlargement commutes
with the actual triangle quotient.

The resulting packet is embedded in the completed all-character GNS space,
the unique global vacuum is removed, and every nonempty sequence of physical
packet transfers contracts squared norm by at most the exact factor `1/64`.
The theorem is instantiated on the actual joint triangle state, not on an
abstract network premise.  A vacuum-external/fundamental-internal triangle is
nonzero and attains `1/64` exactly.

The original parity fence remains in force: for the all-fundamental triangle,
independent edge factorization is `1/512`, while the simultaneous quotient is
zero.

Honest scope: this is one three-vertex graph with nine independent cutoffs and
its completed projected transfer edge.  It is not an arbitrary finite graph,
thermodynamic limit, or continuum Yang--Mills construction.
-/

import YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork
import YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap
import YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope

namespace YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection
open YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteSpinNetworkGlobalVacuumEnvelope
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2FiniteTrivalentTriangleNetwork

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_eqv_congr (f g : Nat → Q')
    (h : ∀ i, f i ≈ g i) (n : Nat) : fsum f n ≈ fsum g n :=
  YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr f g h n

private theorem packetEqv_trans {K : Nat} {P Q R : CharacterPacket K}
    (hPQ : PacketEqv P Q) (hQR : PacketEqv Q R) : PacketEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

private theorem embedV_eq_of_packetEqv {K : Nat}
    {P Q : CharacterPacket K} (h : PacketEqv P Q) :
    embedV packetColimitGNS (stagePacket P) =
      embedV packetColimitGNS (stagePacket Q) := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => coeffAt_packetEqv h s))

private theorem embedV_stage_pad_eq {K L : Nat} (hKL : K ≤ L)
    (P : CharacterPacket K) :
    embedV packetColimitGNS (stagePacket (padPacket hKL P)) =
      embedV packetColimitGNS (stagePacket P) := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => by
      change coeffAt (padPacket hKL P) s ≈ coeffAt P s
      rw [coeffAt_padPacket]
      exact Q'.eqv_refl _))

/-! ## Nine independent cutoffs -/

/-- A deliberately simple canonical common cutoff.  The sum, rather than a
nested maximum, makes all nine inclusion and monotonicity proofs transparent
while preserving exact directed-system coherence. -/
def triangleCutoff9
    (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) : Nat :=
  A0 + B0 + E0 + A1 + B1 + E1 + A2 + B2 + E2

private theorem tc9_le_A0 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    A0 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_B0 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    B0 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_E0 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    E0 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_A1 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    A1 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_B1 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    B1 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_E1 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    E1 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_A2 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    A2 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_B2 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    B2 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

private theorem tc9_le_E2 (A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat) :
    E2 ≤ triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 := by
  unfold triangleCutoff9
  omega

/-- Place nine independently truncated decorations on the concrete common
triangle carrier. -/
def arbitraryTrianglePacketNetwork
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    TrianglePacketNetwork (triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2) where
  edge01At0 := padPacket (tc9_le_A0 A0 B0 E0 A1 B1 E1 A2 B2 E2) P01At0
  edge20At0 := padPacket (tc9_le_B0 A0 B0 E0 A1 B1 E1 A2 B2 E2) P20At0
  external0 := padPacket (tc9_le_E0 A0 B0 E0 A1 B1 E1 A2 B2 E2) X0
  edge01At1 := padPacket (tc9_le_A1 A0 B0 E0 A1 B1 E1 A2 B2 E2) P01At1
  edge12At1 := padPacket (tc9_le_B1 A0 B0 E0 A1 B1 E1 A2 B2 E2) P12At1
  external1 := padPacket (tc9_le_E1 A0 B0 E0 A1 B1 E1 A2 B2 E2) X1
  edge12At2 := padPacket (tc9_le_A2 A0 B0 E0 A1 B1 E1 A2 B2 E2) P12At2
  edge20At2 := padPacket (tc9_le_B2 A0 B0 E0 A1 B1 E1 A2 B2 E2) P20At2
  external2 := padPacket (tc9_le_E2 A0 B0 E0 A1 B1 E1 A2 B2 E2) X2

def arbitraryTriangleJointPacket
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    CharacterPacket (triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2) :=
  triangleJointPacket
    (arbitraryTrianglePacketNetwork P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

def arbitraryTriangleJointPacketCyclic
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    CharacterPacket (triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2) :=
  triangleJointPacketCyclic
    (arbitraryTrianglePacketNetwork P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

def arbitraryTriangleJointPacketOrientationReverse
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    CharacterPacket (triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2) :=
  triangleJointPacketOrientationReverse
    (arbitraryTrianglePacketNetwork P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

theorem arbitraryTriangleJointPacket_association
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    PacketEqv
      (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2)
      (arbitraryTriangleJointPacketCyclic P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2) :=
  triangleJointPacket_association _

theorem arbitraryTriangleJointPacket_orientation
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    PacketEqv
      (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2)
      (arbitraryTriangleJointPacketOrientationReverse P01At0 P20At0 X0
        P01At1 P12At1 X1 P12At2 P20At2 X2) :=
  triangleJointPacket_orientation _

private theorem triangleCutoff9_mono
    {A0 A0' B0 B0' E0 E0' A1 A1' B1 B1' E1 E1'
      A2 A2' B2 B2' E2 E2' : Nat}
    (hA0 : A0 ≤ A0') (hB0 : B0 ≤ B0') (hE0 : E0 ≤ E0')
    (hA1 : A1 ≤ A1') (hB1 : B1 ≤ B1') (hE1 : E1 ≤ E1')
    (hA2 : A2 ≤ A2') (hB2 : B2 ≤ B2') (hE2 : E2 ≤ E2') :
    triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2 ≤
      triangleCutoff9 A0' B0' E0' A1' B1' E1' A2' B2' E2' := by
  unfold triangleCutoff9
  omega

private theorem pad_path_eqv
    {N N' K K' : Nat} (hNN : N ≤ N') (hNK : N ≤ K)
    (hN'K' : N' ≤ K') (hKK : K ≤ K') (P : CharacterPacket N) :
    PacketEqv (padPacket hN'K' (padPacket hNN P))
      (padPacket hKK (padPacket hNK P)) := by
  intro i
  change coeffAt (padPacket hNN P) i.val ≈ coeffAt (padPacket hNK P) i.val
  simp only [coeffAt_padPacket]
  exact Q'.eqv_refl _

/-- Nine unrelated cutoff enlargements commute with the actual simultaneous
triangle quotient. -/
theorem arbitraryTriangleJointPacket_pad_independent
    {A0 A0' B0 B0' E0 E0' A1 A1' B1 B1' E1 E1'
      A2 A2' B2 B2' E2 E2' : Nat}
    (hA0 : A0 ≤ A0') (hB0 : B0 ≤ B0') (hE0 : E0 ≤ E0')
    (hA1 : A1 ≤ A1') (hB1 : B1 ≤ B1') (hE1 : E1 ≤ E1')
    (hA2 : A2 ≤ A2') (hB2 : B2 ≤ B2') (hE2 : E2 ≤ E2')
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    PacketEqv
      (arbitraryTriangleJointPacket
        (padPacket hA0 P01At0) (padPacket hB0 P20At0) (padPacket hE0 X0)
        (padPacket hA1 P01At1) (padPacket hB1 P12At1) (padPacket hE1 X1)
        (padPacket hA2 P12At2) (padPacket hB2 P20At2) (padPacket hE2 X2))
      (padPacket
        (triangleCutoff9_mono hA0 hB0 hE0 hA1 hB1 hE1 hA2 hB2 hE2)
        (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1 P12At1 X1
          P12At2 P20At2 X2)) := by
  let K := triangleCutoff9 A0 B0 E0 A1 B1 E1 A2 B2 E2
  let K' := triangleCutoff9 A0' B0' E0' A1' B1' E1' A2' B2' E2'
  have hKK : K ≤ K' :=
    triangleCutoff9_mono hA0 hB0 hE0 hA1 hB1 hE1 hA2 hB2 hE2
  let T : TrianglePacketNetwork K :=
    arbitraryTrianglePacketNetwork P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2
  let T' : TrianglePacketNetwork K' :=
    arbitraryTrianglePacketNetwork
      (padPacket hA0 P01At0) (padPacket hB0 P20At0) (padPacket hE0 X0)
      (padPacket hA1 P01At1) (padPacket hB1 P12At1) (padPacket hE1 X1)
      (padPacket hA2 P12At2) (padPacket hB2 P20At2) (padPacket hE2 X2)
  have hTT : TrianglePacketNetworkEqv T' (padTrianglePacketNetwork hKK T) := by
    constructor
    · exact pad_path_eqv hA0 (tc9_le_A0 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_A0 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P01At0
    · exact pad_path_eqv hB0 (tc9_le_B0 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_B0 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P20At0
    · exact pad_path_eqv hE0 (tc9_le_E0 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_E0 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK X0
    · exact pad_path_eqv hA1 (tc9_le_A1 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_A1 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P01At1
    · exact pad_path_eqv hB1 (tc9_le_B1 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_B1 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P12At1
    · exact pad_path_eqv hE1 (tc9_le_E1 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_E1 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK X1
    · exact pad_path_eqv hA2 (tc9_le_A2 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_A2 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P12At2
    · exact pad_path_eqv hB2 (tc9_le_B2 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_B2 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK P20At2
    · exact pad_path_eqv hE2 (tc9_le_E2 A0 B0 E0 A1 B1 E1 A2 B2 E2)
        (tc9_le_E2 A0' B0' E0' A1' B1' E1' A2' B2' E2') hKK X2
  change PacketEqv (triangleJointPacket T')
    (padPacket hKK (triangleJointPacket T))
  exact packetEqv_trans (triangleJointPacket_congr hTT)
    (triangleJointPacket_pad hKK T)

/-! ## Exact connection to the finite-network spectral envelope -/

def triangleEdgeOrder : List Nat := [0, 1, 2]

def triangleEdgeLabel (a b c edge : Nat) : Nat :=
  if edge = 0 then a else if edge = 1 then b else if edge = 2 then c else 0

/-- The product eigenvalue used by the finite-network spectral envelope is
exactly the three-edge weight appearing in the joint triangle sum. -/
theorem triangleNetworkEigen_exact (a b c : Nat) :
    networkEigen triangleEdgeOrder (triangleEdgeLabel a b c) ≈
      packetEigen a * (packetEigen b * packetEigen c) := by
  unfold networkEigen triangleEdgeOrder triangleEdgeLabel
    YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork.eliminateLinks
    packetEigen
  simp only [ite_true, OfNat.ofNat, Nat.reduceEqDiff]
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))

private theorem triangleModeExcited_of_nonempty {a b c : Nat}
    (h : 1 ≤ a ∨ 1 ≤ b ∨ 1 ≤ c) :
    ModeExcited triangleEdgeOrder (triangleEdgeLabel a b c) := by
  rcases h with ha | hb | hc
  · exact ⟨0, by simp [triangleEdgeOrder], by simpa [triangleEdgeLabel]⟩
  · exact ⟨1, by simp [triangleEdgeOrder], by simpa [triangleEdgeLabel]⟩
  · exact ⟨2, by simp [triangleEdgeOrder], by simpa [triangleEdgeLabel]⟩

/-- Every nonempty actual triangle labeling lies below the finite-network
global-vacuum separator `1/64`.  This specializes the envelope to the three
labels used by the concrete joint evaluator. -/
theorem triangleNetworkSquaredEigen_nonempty_one_over_64
    (a b c : Nat) (h : 1 ≤ a ∨ 1 ≤ b ∨ 1 ≤ c) :
    networkEigen triangleEdgeOrder (triangleEdgeLabel a b c) *
        networkEigen triangleEdgeOrder (triangleEdgeLabel a b c) ≤
      Q'.mkPos 1 64 (by decide) := by
  have hmode := triangleModeExcited_of_nonempty h
  have hsep := globalVacuumFamilySquaredEigen_le_sep triangleEdgeOrder
    (fun _ => triangleEdgeLabel a b c) 0
  rw [globalVacuumFamilySquaredEigen, if_pos hmode] at hsep
  exact Q'.le_trans' _ _ _ hsep
    (Q'.le_of_eqv finiteNetworkSquaredSep_exact)

/-- Re-expression of the actual joint triangle scalar in the spectral
envelope's three-edge eigenvalue. -/
theorem triangleJointGram_networkEigen {K : Nat}
    (T : TrianglePacketNetwork K) :
    triangleJointGram T ≈
      fsum (fun a => fsum (fun b => fsum (fun c =>
        networkEigen triangleEdgeOrder (triangleEdgeLabel a b c) *
          triangleIntegrand T a b c) (K + 1)) (K + 1)) (K + 1) := by
  refine Q'.eqv_trans _ _ _ (triangleJointGram_common_triple T) ?_
  exact fsum_eqv_congr _ _ (fun a =>
    fsum_eqv_congr _ _ (fun b =>
      fsum_eqv_congr _ _ (fun c => by
        apply Q'.mul_eqv_congr_right
        refine Q'.eqv_trans _ (packetEigen a *
          (packetEigen b * packetEigen c)) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        exact Q'.eqv_symm (triangleNetworkEigen_exact a b c)) (K + 1))
      (K + 1)) (K + 1)

/-! ## Completed arbitrary triangle state -/

def completedArbitraryTriangleJointState
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) : GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1
      P12At1 X1 P12At2 P20At2 X2))

def completedArbitraryTriangleCyclicState
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) : GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (arbitraryTriangleJointPacketCyclic P01At0 P20At0 X0
      P01At1 P12At1 X1 P12At2 P20At2 X2))

def completedArbitraryTriangleOrientationReverseState
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) : GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (arbitraryTriangleJointPacketOrientationReverse P01At0 P20At0
      X0 P01At1 P12At1 X1 P12At2 P20At2 X2))

theorem completedArbitraryTriangle_association
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 =
      completedArbitraryTriangleCyclicState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 :=
  embedV_eq_of_packetEqv
    (arbitraryTriangleJointPacket_association P01At0 P20At0 X0 P01At1
      P12At1 X1 P12At2 P20At2 X2)

theorem completedArbitraryTriangle_orientation
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 =
      completedArbitraryTriangleOrientationReverseState P01At0 P20At0 X0
        P01At1 P12At1 X1 P12At2 P20At2 X2 :=
  embedV_eq_of_packetEqv
    (arbitraryTriangleJointPacket_orientation P01At0 P20At0 X0 P01At1
      P12At1 X1 P12At2 P20At2 X2)

theorem completedArbitraryTriangle_pad_independent
    {A0 A0' B0 B0' E0 E0' A1 A1' B1 B1' E1 E1'
      A2 A2' B2 B2' E2 E2' : Nat}
    (hA0 : A0 ≤ A0') (hB0 : B0 ≤ B0') (hE0 : E0 ≤ E0')
    (hA1 : A1 ≤ A1') (hB1 : B1 ≤ B1') (hE1 : E1 ≤ E1')
    (hA2 : A2 ≤ A2') (hB2 : B2 ≤ B2') (hE2 : E2 ≤ E2')
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleJointState
        (padPacket hA0 P01At0) (padPacket hB0 P20At0) (padPacket hE0 X0)
        (padPacket hA1 P01At1) (padPacket hB1 P12At1) (padPacket hE1 X1)
        (padPacket hA2 P12At2) (padPacket hB2 P20At2) (padPacket hE2 X2) =
      completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 := by
  refine Eq.trans (embedV_eq_of_packetEqv
    (arbitraryTriangleJointPacket_pad_independent
      hA0 hB0 hE0 hA1 hB1 hE1 hA2 hB2 hE2 P01At0 P20At0 X0
      P01At1 P12At1 X1 P12At2 P20At2 X2)) ?_
  exact embedV_stage_pad_eq
    (triangleCutoff9_mono hA0 hB0 hE0 hA1 hB1 hE1 hA2 hB2 hE2)
    (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

theorem completedArbitraryTriangle_transfer_exact
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedPacketTransfer
        (completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1
          P12At1 X1 P12At2 P20At2 X2) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer
          (arbitraryTriangleJointPacket P01At0 P20At0 X0 P01At1 P12At1 X1
            P12At2 P20At2 X2))) :=
  completedPacketTransfer_embed _

/-! ## Canonical global-vacuum projection and the completed gap -/

def completedArbitraryTriangleProjectedState
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) : GNSCompletionSpace packetColimitGNS :=
  completedRemoveVacuum
    (completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

theorem completedArbitraryTriangleProjectedState_fixed
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedRemoveVacuum
        (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
          P12At1 X1 P12At2 P20At2 X2) =
      completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
        P12At1 X1 P12At2 P20At2 X2 := by
  exact completedRemoveVacuum_idempotent _

theorem completedArbitraryTriangleProjected_association
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 =
      completedRemoveVacuum
        (completedArbitraryTriangleCyclicState P01At0 P20At0 X0 P01At1 P12At1 X1
          P12At2 P20At2 X2) :=
  congrArg completedRemoveVacuum
    (completedArbitraryTriangle_association P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

theorem completedArbitraryTriangleProjected_orientation
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 =
      completedRemoveVacuum
        (completedArbitraryTriangleOrientationReverseState P01At0 P20At0 X0
          P01At1 P12At1 X1 P12At2 P20At2 X2) :=
  congrArg completedRemoveVacuum
    (completedArbitraryTriangle_orientation P01At0 P20At0 X0 P01At1 P12At1 X1
      P12At2 P20At2 X2)

theorem completedArbitraryTriangleProjected_pad_independent
    {A0 A0' B0 B0' E0 E0' A1 A1' B1 B1' E1 E1'
      A2 A2' B2 B2' E2 E2' : Nat}
    (hA0 : A0 ≤ A0') (hB0 : B0 ≤ B0') (hE0 : E0 ≤ E0')
    (hA1 : A1 ≤ A1') (hB1 : B1 ≤ B1') (hE1 : E1 ≤ E1')
    (hA2 : A2 ≤ A2') (hB2 : B2 ≤ B2') (hE2 : E2 ≤ E2')
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedArbitraryTriangleProjectedState
        (padPacket hA0 P01At0) (padPacket hB0 P20At0) (padPacket hE0 X0)
        (padPacket hA1 P01At1) (padPacket hB1 P12At1) (padPacket hE1 X1)
        (padPacket hA2 P12At2) (padPacket hB2 P20At2) (padPacket hE2 X2) =
      completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1 P12At1 X1
        P12At2 P20At2 X2 :=
  congrArg completedRemoveVacuum
    (completedArbitraryTriangle_pad_independent
      hA0 hB0 hE0 hA1 hB1 hE1 hA2 hB2 hE2 P01At0 P20At0 X0
      P01At1 P12At1 X1 P12At2 P20At2 X2)

theorem completedArbitraryTriangleProjected_transfer_commutes
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    completedPacketTransfer
        (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
          P12At1 X1 P12At2 P20At2 X2) =
      completedRemoveVacuum
        (completedPacketTransfer
          (completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2)) := by
  exact completedRemoveVacuum_transfer_commute _

/-- The actual projected joint triangle state contracts in squared norm by
the exact nonempty-mode separator `1/64`. -/
theorem completedArbitraryTriangleProjected_uniform_one_over_64
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2))
        (completedPacketTransfer
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2)))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2)
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2))) := by
  simpa [completedPacketCycleTransfer, completedArbitraryTriangleProjectedState,
    completedRemoveVacuum_idempotent] using
      (completedPacketCycleTransfer_projected_uniform_one_over_64 0 []
        (completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1
          P12At1 X1 P12At2 P20At2 X2))

/-- Any nonempty finite transfer sequence retains the same `1/64` squared
separator; later links are contractive. -/
theorem completedArbitraryTriangleProjected_cycle_uniform_one_over_64
    {A0 B0 E0 A1 B1 E1 A2 B2 E2 : Nat}
    (l : Nat) (rest : List Nat)
    (P01At0 : CharacterPacket A0) (P20At0 : CharacterPacket B0)
    (X0 : CharacterPacket E0) (P01At1 : CharacterPacket A1)
    (P12At1 : CharacterPacket B1) (X1 : CharacterPacket E1)
    (P12At2 : CharacterPacket A2) (P20At2 : CharacterPacket B2)
    (X2 : CharacterPacket E2) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer (l :: rest)
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2))
        (completedPacketCycleTransfer (l :: rest)
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2)))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2)
          (completedArbitraryTriangleProjectedState P01At0 P20At0 X0 P01At1
            P12At1 X1 P12At2 P20At2 X2))) := by
  simpa [completedArbitraryTriangleProjectedState,
    completedRemoveVacuum_idempotent] using
      (completedPacketCycleTransfer_projected_uniform_one_over_64 l rest
        (completedArbitraryTriangleJointState P01At0 P20At0 X0 P01At1
          P12At1 X1 P12At2 P20At2 X2))

/-! ## Concrete nonzero sharp witness and preserved parity fence -/

def triangleVacuumExternal : CharacterPacket 1 := vacuumPacket 1

/-- All three internal edges are fundamental, while every external leg is
vacuum.  Hence each local constraint is `N_{11}^0 = 1`, so the simultaneous
triangle quotient is nonzero. -/
def fundamentalVacuumTriangleNetwork : TrianglePacketNetwork 1 where
  edge01At0 := trivalentFundamentalLeg
  edge20At0 := trivalentFundamentalLeg
  external0 := triangleVacuumExternal
  edge01At1 := trivalentFundamentalLeg
  edge12At1 := trivalentFundamentalLeg
  external1 := triangleVacuumExternal
  edge12At2 := trivalentFundamentalLeg
  edge20At2 := trivalentFundamentalLeg
  external2 := triangleVacuumExternal

def fundamentalVacuumTrianglePacket : CharacterPacket 1 :=
  triangleJointPacket fundamentalVacuumTriangleNetwork

theorem fundamentalVacuumTrianglePacket_zero :
    coeffAt fundamentalVacuumTrianglePacket 0 ≈ 0 := by decide

/-- The two eliminated fundamental edges each contribute `1/8`. -/
theorem fundamentalVacuumTrianglePacket_one :
    coeffAt fundamentalVacuumTrianglePacket 1 ≈
      Q'.mkPos 1 64 (by decide) := by decide

/-- Exact nonzero Wilson squared norm of the actual joint triangle packet. -/
theorem fundamentalVacuumTrianglePacket_norm_exact :
    packetWilsonGram fundamentalVacuumTrianglePacket
      fundamentalVacuumTrianglePacket ≈
        Q'.mkPos 1 32768 (by decide) := by decide

theorem fundamentalVacuumTrianglePacket_norm_nonzero :
    ¬ (packetWilsonGram fundamentalVacuumTrianglePacket
      fundamentalVacuumTrianglePacket ≈ 0) := by decide

/-- Exact squared norm after one physical transfer of the retained edge. -/
theorem fundamentalVacuumTrianglePacket_transfer_norm_exact :
    packetWilsonGram (packetTransfer fundamentalVacuumTrianglePacket)
      (packetTransfer fundamentalVacuumTrianglePacket) ≈
        Q'.mkPos 1 2097152 (by decide) := by decide

/-- The concrete nonzero triangle attains the `1/64` squared factor. -/
theorem fundamentalVacuumTrianglePacket_sharp_one_over_64 :
    packetWilsonGram (packetTransfer fundamentalVacuumTrianglePacket)
        (packetTransfer fundamentalVacuumTrianglePacket) ≈
      Q'.mkPos 1 64 (by decide) *
        packetWilsonGram fundamentalVacuumTrianglePacket
          fundamentalVacuumTrianglePacket := by decide

def completedFundamentalVacuumTriangleProjectedState :
    GNSCompletionSpace packetColimitGNS :=
  completedRemoveVacuum
    (completedTriangleJointState fundamentalVacuumTriangleNetwork)

/-- The global-vacuum projector leaves the explicit nonzero joint packet
unchanged; its vacuum coefficient vanishes before completion. -/
theorem completedFundamentalVacuumTriangleProjectedState_eq :
    completedFundamentalVacuumTriangleProjectedState =
      completedTriangleJointState fundamentalVacuumTriangleNetwork := by
  unfold completedFundamentalVacuumTriangleProjectedState
    completedTriangleJointState
  apply completedRemoveVacuum_embed_vacuumFree
  simpa [fundamentalVacuumTrianglePacket] using
    fundamentalVacuumTrianglePacket_zero

/-- Concrete completed projected norm inequality for the nonzero sharp
triangle witness. -/
theorem completedFundamentalVacuumTriangleProjected_uniform_one_over_64 :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer completedFundamentalVacuumTriangleProjectedState)
        (completedPacketTransfer completedFundamentalVacuumTriangleProjectedState))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          completedFundamentalVacuumTriangleProjectedState
          completedFundamentalVacuumTriangleProjectedState)) := by
  simpa [completedPacketCycleTransfer,
    completedFundamentalVacuumTriangleProjectedState,
    completedRemoveVacuum_idempotent] using
      (completedPacketCycleTransfer_projected_uniform_one_over_64 0 []
        (completedTriangleJointState fundamentalVacuumTriangleNetwork))

/-- The earlier `1/512`-versus-zero guard is re-exported as one theorem so a
future graph evaluator cannot silently replace the joint triangle by the
independent-edge product. -/
theorem fundamentalTriangleParityFence_preserved :
    fundamentalTriangleIndependentEdgeGram ≈ Q'.mkPos 1 512 (by decide) ∧
    fundamentalTriangleSimultaneousGram ≈ 0 ∧
    ¬ (fundamentalTriangleIndependentEdgeGram ≈
      fundamentalTriangleSimultaneousGram) :=
  ⟨fundamental_triangle_independent_exact,
    fundamental_triangle_simultaneous_zero,
    fundamental_triangle_independent_disagrees⟩

end YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap

#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.arbitraryTriangleJointPacket_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.arbitraryTriangleJointPacket_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.arbitraryTriangleJointPacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.triangleNetworkEigen_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.triangleNetworkSquaredEigen_nonempty_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.triangleJointGram_networkEigen
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangle_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangle_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangle_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangle_transfer_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjectedState_fixed
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_transfer_commutes
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_uniform_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedArbitraryTriangleProjected_cycle_uniform_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_one
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_norm_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_norm_nonzero
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_transfer_norm_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalVacuumTrianglePacket_sharp_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedFundamentalVacuumTriangleProjectedState_eq
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.completedFundamentalVacuumTriangleProjected_uniform_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketTriangleCompletedGap.fundamentalTriangleParityFence_preserved
