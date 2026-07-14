/-
# Two arbitrary trivalent vertices glued on one common packet edge

Each endpoint is the arbitrary-cutoff trivalent carrier constructed in
`SU2ArbitraryPacketTrivalentVertexCompatibility`.  After taking its local
association quotient, the endpoint exposes one fused character packet.  The
two exposed packets are glued by a *single common-label* Wilson/Haar
contraction: both are padded to one cutoff and the same irreducible label is
summed once.  This is not a product of independently eliminated vertices.

The local association trees and full orientation reversals may be changed at
either endpoint without changing the contraction.  All six original packet
cutoffs may also grow independently.  The corresponding completed endpoint
pair and physical transfer descend through both local quotients.

An exact normalization fence records why the naive tensor-product vacuum
contraction is wrong: two all-fundamental trivalent endpoints each have zero
vacuum coefficient, so the product of their separate vacuum values is zero,
whereas their common-label contraction is nonzero.  The corrected diagonal
sum retains the shared `chi_1` and `chi_3` channels.

Honest scope: this closes one edge joining two trivalent class-packet
vertices.  It does not yet impose all vertex and cycle quotients of a general
finite lattice, construct its partition functional, or control volume and
continuum limits.
-/

import YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility

namespace YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility

local infix:50 " ≈ " => Q'.eqv

private theorem packetEqv_refl {K : Nat} (P : CharacterPacket K) :
    PacketEqv P P := fun _ => Q'.eqv_refl _

private theorem stagedEqv_of_packetEqv {K : Nat}
    {P Q : CharacterPacket K} (h : PacketEqv P Q) :
    StagedEqv (stagePacket P) (stagePacket Q) := by
  intro s
  exact coeffAt_packetEqv h s

private theorem stagedGram_congr_right (A : StagedPacket)
    {B B' : StagedPacket} (hBB : StagedEqv B B') :
    stagedGram A B ≈ stagedGram A B' := by
  refine Q'.eqv_trans _ (stagedGram B A) _ (stagedGram_symm A B) ?_
  refine Q'.eqv_trans _ (stagedGram B' A) _
    (stagedGram_congr_left A hBB) ?_
  exact Q'.eqv_symm (stagedGram_symm A B')

/-! ## One common-label contraction after both local quotients -/

/-- The left association representative exposed by a trivalent endpoint. -/
def exposedLeftStage {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : StagedPacket :=
  stagePacket (arbitraryTrivalentVertexPacket P Q R).1

/-- The right association representative of the same endpoint quotient. -/
def exposedRightStage {N M L : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) : StagedPacket :=
  stagePacket (arbitraryTrivalentVertexPacket P Q R).2

/-- Corrected gluing of two trivalent endpoints.  `stagedGram` pads their
possibly different output cutoffs to one maximum and contracts one common
irreducible label. -/
def twoVertexGluingGram
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) : Q' :=
  stagedGram (exposedLeftStage P₁ Q₁ R₁)
    (exposedLeftStage P₂ Q₂ R₂)

/-- The common-label nature of the contraction is explicit: there is one
diagonal sum, not a product of two independent vertex sums. -/
theorem twoVertexGluingGram_common_label
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      fsum (fun s => packetEigen s *
        (coeffAt
            (padPacket
              (Nat.le_max_left
                (trivalentOutputCutoff (trivalentCutoff N₁ M₁ L₁))
                (trivalentOutputCutoff (trivalentCutoff N₂ M₂ L₂)))
              (arbitraryTrivalentVertexPacket P₁ Q₁ R₁).1) s *
          coeffAt
            (padPacket
              (Nat.le_max_right
                (trivalentOutputCutoff (trivalentCutoff N₁ M₁ L₁))
                (trivalentOutputCutoff (trivalentCutoff N₂ M₂ L₂)))
              (arbitraryTrivalentVertexPacket P₂ Q₂ R₂).1) s))
        (Nat.max
          (trivalentOutputCutoff (trivalentCutoff N₁ M₁ L₁))
          (trivalentOutputCutoff (trivalentCutoff N₂ M₂ L₂)) + 1) := by
  unfold twoVertexGluingGram exposedLeftStage stagedGram
  exact packetWilsonGram_diagonal _ _

/-- Both endpoint association quotients are imposed simultaneously.  All four
choices of local tree give the same shared-edge contraction. -/
theorem twoVertexGluingGram_association_independent
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram (exposedRightStage P₁ Q₁ R₁)
        (exposedLeftStage P₂ Q₂ R₂) ∧
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram (exposedLeftStage P₁ Q₁ R₁)
        (exposedRightStage P₂ Q₂ R₂) ∧
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram (exposedRightStage P₁ Q₁ R₁)
        (exposedRightStage P₂ Q₂ R₂) := by
  let h₁ : StagedEqv (exposedLeftStage P₁ Q₁ R₁)
      (exposedRightStage P₁ Q₁ R₁) :=
    stagedEqv_of_packetEqv
      (arbitraryTrivalent_association_closure P₁ Q₁ R₁)
  let h₂ : StagedEqv (exposedLeftStage P₂ Q₂ R₂)
      (exposedRightStage P₂ Q₂ R₂) :=
    stagedEqv_of_packetEqv
      (arbitraryTrivalent_association_closure P₂ Q₂ R₂)
  refine ⟨stagedGram_congr_left _ h₁,
    stagedGram_congr_right _ h₂, ?_⟩
  exact Q'.eqv_trans _
    (stagedGram (exposedRightStage P₁ Q₁ R₁)
      (exposedLeftStage P₂ Q₂ R₂)) _
    (stagedGram_congr_left _ h₁)
    (stagedGram_congr_right _ h₂)

/-! ## Independent cutoff and orientation coherence -/

private theorem trivalentCutoff_mono_local
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L') :
    trivalentCutoff N M L ≤ trivalentCutoff N' M' L' := by
  unfold trivalentCutoff
  apply (Nat.max_le).2
  exact ⟨Nat.le_trans hN (Nat.le_max_left _ _),
    (Nat.max_le).2
      ⟨Nat.le_trans hM
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
        Nat.le_trans hL
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩⟩

private theorem exposedLeftStage_pad_independent
    {N N' M M' L L' : Nat}
    (hN : N ≤ N') (hM : M ≤ M') (hL : L ≤ L')
    (P : CharacterPacket N) (Q : CharacterPacket M)
    (R : CharacterPacket L) :
    StagedEqv
      (exposedLeftStage (padPacket hN P) (padPacket hM Q) (padPacket hL R))
      (exposedLeftStage P Q R) := by
  have hv := arbitraryTrivalentVertexPacket_pad_independent hN hM hL P Q R
  intro s
  refine Q'.eqv_trans _
    (coeffAt
      (padPacket
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
          (trivalentCutoff_mono_local hN hM hL)))
        (arbitraryTrivalentVertexPacket P Q R).1) s) _ ?_ ?_
  · exact coeffAt_packetEqv hv.1 s
  · rw [coeffAt_padPacket]
    exact Q'.eqv_refl _

/-- All six original endpoint cutoffs may grow independently without changing
the corrected common-label contraction. -/
theorem twoVertexGluingGram_pad_independent
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    twoVertexGluingGram (padPacket hN₁ P₁) (padPacket hM₁ Q₁)
        (padPacket hL₁ R₁) (padPacket hN₂ P₂)
        (padPacket hM₂ Q₂) (padPacket hL₂ R₂) ≈
      twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ := by
  unfold twoVertexGluingGram
  refine Q'.eqv_trans _
    (stagedGram (exposedLeftStage P₁ Q₁ R₁)
      (exposedLeftStage (padPacket hN₂ P₂) (padPacket hM₂ Q₂)
        (padPacket hL₂ R₂))) _ ?_ ?_
  · exact stagedGram_congr_left _
      (exposedLeftStage_pad_independent hN₁ hM₁ hL₁ P₁ Q₁ R₁)
  · exact stagedGram_congr_right _
      (exposedLeftStage_pad_independent hN₂ hM₂ hL₂ P₂ Q₂ R₂)

/-- Reversing all incident orientations at either endpoint leaves the glued
common-label Gram unchanged. -/
theorem twoVertexGluingGram_orientation_invariant
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram
        (stagePacket (arbitraryTrivalentOrientationReverse P₁ Q₁ R₁).1)
        (exposedLeftStage P₂ Q₂ R₂) ∧
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram
        (exposedLeftStage P₁ Q₁ R₁)
        (stagePacket
          (arbitraryTrivalentOrientationReverse P₂ Q₂ R₂).1) ∧
    twoVertexGluingGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      stagedGram
        (stagePacket (arbitraryTrivalentOrientationReverse P₁ Q₁ R₁).1)
        (stagePacket
          (arbitraryTrivalentOrientationReverse P₂ Q₂ R₂).1) := by
  let h₁ : StagedEqv (exposedLeftStage P₁ Q₁ R₁)
      (stagePacket (arbitraryTrivalentOrientationReverse P₁ Q₁ R₁).1) :=
    stagedEqv_of_packetEqv
      (arbitraryTrivalent_orientation_reversal P₁ Q₁ R₁).1
  let h₂ : StagedEqv (exposedLeftStage P₂ Q₂ R₂)
      (stagePacket (arbitraryTrivalentOrientationReverse P₂ Q₂ R₂).1) :=
    stagedEqv_of_packetEqv
      (arbitraryTrivalent_orientation_reversal P₂ Q₂ R₂).1
  unfold twoVertexGluingGram
  refine ⟨stagedGram_congr_left _ h₁,
    stagedGram_congr_right _ h₂, ?_⟩
  exact Q'.eqv_trans _
    (stagedGram
      (stagePacket (arbitraryTrivalentOrientationReverse P₁ Q₁ R₁).1)
      (exposedLeftStage P₂ Q₂ R₂)) _
    (stagedGram_congr_left _ h₁)
    (stagedGram_congr_right _ h₂)

/-! ## Exact fence against independent vacuum contraction -/

/-- Naive product of separately eliminated endpoint vacua. -/
def fundamentalNaiveVertexVacuumProduct : Q' :=
  vacuumHaar
      (leftAssociatedPacket trivalentFundamentalLeg trivalentFundamentalLeg
        trivalentFundamentalLeg) *
    vacuumHaar
      (leftAssociatedPacket trivalentFundamentalLeg trivalentFundamentalLeg
        trivalentFundamentalLeg)

/-- Correct common-label contraction of the same two endpoints. -/
def fundamentalTwoVertexCommonLabelGram : Q' :=
  packetWilsonGram
    (leftAssociatedPacket trivalentFundamentalLeg trivalentFundamentalLeg
      trivalentFundamentalLeg)
    (leftAssociatedPacket trivalentFundamentalLeg trivalentFundamentalLeg
      trivalentFundamentalLeg)

theorem fundamental_naive_vacuum_product_zero :
    fundamentalNaiveVertexVacuumProduct ≈ 0 := by decide

/-- **Banked sharp fence.**  Independent vacuum elimination loses the shared
odd channels: it gives zero, while the common-label Wilson contraction is
exactly `4*(1/8) + 1/32768`. -/
theorem fundamental_common_label_gram_exact :
    fundamentalTwoVertexCommonLabelGram ≈
      Q'.mkPos 16385 32768 (by decide) := by decide

theorem fundamental_naive_tensor_gluing_false :
    ¬ (fundamentalTwoVertexCommonLabelGram ≈
      fundamentalNaiveVertexVacuumProduct) := by decide

/-! ## Completion and transfer descent -/

/-- Completed exposed-edge pair for the two endpoints. -/
def completedTwoVertexEdgeState
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  ((completedArbitraryTrivalentState P₁ Q₁ R₁).1,
    (completedArbitraryTrivalentState P₂ Q₂ R₂).1)

/-- The completed glued-edge pair is invariant under six independent input
cutoff enlargements. -/
theorem completedTwoVertexEdgeState_pad_independent
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedTwoVertexEdgeState
        (padPacket hN₁ P₁) (padPacket hM₁ Q₁) (padPacket hL₁ R₁)
        (padPacket hN₂ P₂) (padPacket hM₂ Q₂) (padPacket hL₂ R₂) =
      completedTwoVertexEdgeState P₁ Q₁ R₁ P₂ Q₂ R₂ := by
  have h₁ := completedArbitraryTrivalentState_pad_independent
    hN₁ hM₁ hL₁ P₁ Q₁ R₁
  have h₂ := completedArbitraryTrivalentState_pad_independent
    hN₂ hM₂ hL₂ P₂ Q₂ R₂
  unfold completedTwoVertexEdgeState
  rw [h₁, h₂]

/-- The completed endpoint pair is independent of choosing the left or right
local association representative at both vertices. -/
theorem completedTwoVertex_association_quotient
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedTwoVertexEdgeState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      ((completedArbitraryTrivalentState P₁ Q₁ R₁).2,
        (completedArbitraryTrivalentState P₂ Q₂ R₂).2) := by
  apply Prod.ext
  · exact completedArbitraryTrivalent_association P₁ Q₁ R₁
  · exact completedArbitraryTrivalent_association P₂ Q₂ R₂

def completedTwoVertexTransfer
    (x : GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS) :
    GNSCompletionSpace packetColimitGNS ×
      GNSCompletionSpace packetColimitGNS :=
  (completedPacketTransfer x.1, completedPacketTransfer x.2)

/-- Completed physical transfer descends through both local association
quotients simultaneously. -/
theorem completedTwoVertex_transfer_descends
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedTwoVertexTransfer
        (completedTwoVertexEdgeState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedTwoVertexTransfer
        ((completedArbitraryTrivalentState P₁ Q₁ R₁).2,
          (completedArbitraryTrivalentState P₂ Q₂ R₂).2) := by
  exact congrArg completedTwoVertexTransfer
    (completedTwoVertex_association_quotient P₁ Q₁ R₁ P₂ Q₂ R₂)

/-- On finite endpoint packets, the descended completed action is exactly the
physical packet transfer on both glued-edge representatives. -/
theorem completedTwoVertex_transfer_exact
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedTwoVertexTransfer
        (completedTwoVertexEdgeState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      (embedV packetColimitGNS
          (stagePacket (packetTransfer
            (arbitraryTrivalentVertexPacket P₁ Q₁ R₁).1)),
        embedV packetColimitGNS
          (stagePacket (packetTransfer
            (arbitraryTrivalentVertexPacket P₂ Q₂ R₂).1))) := by
  apply Prod.ext
  · exact completedPacketTransfer_embed (exposedLeftStage P₁ Q₁ R₁)
  · exact completedPacketTransfer_embed (exposedLeftStage P₂ Q₂ R₂)

end YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing

#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.twoVertexGluingGram_common_label
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.twoVertexGluingGram_association_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.twoVertexGluingGram_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.twoVertexGluingGram_orientation_invariant
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.fundamental_naive_vacuum_product_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.fundamental_common_label_gram_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.fundamental_naive_tensor_gluing_false
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.completedTwoVertexEdgeState_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.completedTwoVertex_association_quotient
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.completedTwoVertex_transfer_descends
#print axioms YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing.completedTwoVertex_transfer_exact
