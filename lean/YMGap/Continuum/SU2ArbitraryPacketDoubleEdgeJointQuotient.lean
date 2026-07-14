/-
# Simultaneous two-edge quotient between trivalent vertices

Two trivalent vertices joined by two shared edges have two common labels
`(a,b)`.  Eliminating those edges independently is wrong: the two labels must
satisfy the trivalent admissibility constraint together with the external leg
at *both* endpoints.  This module therefore forms the endpoint fibers first,

    V(P,Q,R;a,b) = P_a Q_b sum_c N_{ab}^c R_c,

and only then contracts the same `(a,b)` at both endpoints.  The resulting
packet is the first-edge marginal after the second edge and both vertex
intertwiner constraints have been imposed simultaneously.

The quotient is independent of the cyclic association used to write the
trivalent multiplicity, invariant under reversal of the two endpoints, and
coherent under cutoff padding.  It embeds into the constructive packet GNS
completion, where physical transfer descends through the joint quotient.

The all-fundamental graph is a sharp fence: independent edge contraction gives
`1/64`, but the simultaneous quotient is zero because `N_{11}^1 = 0` at both
vertices.  Thus the correction is forced by the exact parity constraint, not
by a normalization convention.

Honest scope: this is the smallest two-vertex/two-shared-edge graph with a
joint intertwiner constraint.  It is not yet a general finite-lattice tensor
network, partition functional, or thermodynamic/continuum construction.
-/

import YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient

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
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge
open YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2ArbitraryPacketTwoTrivalentVertexGluing

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem packetEqv_trans {K : Nat} {P Q R : CharacterPacket K}
    (hPQ : PacketEqv P Q) (hQR : PacketEqv Q R) : PacketEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

private theorem fsum_eqv_congr (f g : Nat → Q')
    (h : ∀ i, f i ≈ g i) (n : Nat) : fsum f n ≈ fsum g n :=
  YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr f g h n

private theorem fsum_zero_extension {f : Nat → Q'} {n m : Nat}
    (hnm : n ≤ m) (hz : ∀ i, n ≤ i → f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm)) (q_add_zero_eqv _)

private theorem fusionInd_cyclic (a b c : Nat) :
    fusionInd a b c = fusionInd b c a := by
  have h : fusionInd b c a = fusionInd a b c := by
    unfold fusionInd
    rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_bt b c a]
    rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab b a c]
  exact h.symm

/-! ## Common-cutoff endpoint fibers and the joint packet -/

/-- One endpoint intertwiner fiber with shared labels `a,b` and its external
packet summed against the exact SU(2) multiplicity. -/
def vertexFiber {K : Nat} (P Q R : CharacterPacket K)
    (a b : Nat) : Q' :=
  (coeffAt P a * coeffAt Q b) *
    fsum (fun c => fusionInd a b c * coeffAt R c) (K + 1)

/-- The same endpoint written with the cyclic association
`N_{bc}^a`. -/
def vertexFiberCyclic {K : Nat} (P Q R : CharacterPacket K)
    (a b : Nat) : Q' :=
  (coeffAt P a * coeffAt Q b) *
    fsum (fun c => fusionInd b c a * coeffAt R c) (K + 1)

theorem vertexFiber_association {K : Nat} (P Q R : CharacterPacket K)
    (a b : Nat) : vertexFiber P Q R a b ≈ vertexFiberCyclic P Q R a b := by
  unfold vertexFiber vertexFiberCyclic
  exact Q'.mul_eqv_congr_left _ _ _
    (fsum_eqv_congr _ _ (fun c => by
      rw [fusionInd_cyclic a b c]
      exact Q'.eqv_refl _) (K + 1))

/-- First-edge marginal after the second shared label and both endpoint
intertwiner fibers have been contracted. -/
def jointCoeff {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K)
    (a : Nat) : Q' :=
  fsum (fun b => packetEigen b *
    (vertexFiber P₁ Q₁ R₁ a b * vertexFiber P₂ Q₂ R₂ a b))
    (K + 1)

def jointCoeffCyclic {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K)
    (a : Nat) : Q' :=
  fsum (fun b => packetEigen b *
    (vertexFiberCyclic P₁ Q₁ R₁ a b *
      vertexFiberCyclic P₂ Q₂ R₂ a b)) (K + 1)

/-- Coefficient-bearing simultaneous quotient, retaining the first common
edge label after all other local labels have been eliminated jointly. -/
def doubleEdgeJointPacket {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    CharacterPacket K where
  coeff i := jointCoeff P₁ Q₁ R₁ P₂ Q₂ R₂ i.val

def doubleEdgeJointPacketCyclic {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    CharacterPacket K where
  coeff i := jointCoeffCyclic P₁ Q₁ R₁ P₂ Q₂ R₂ i.val

/-- Both local association choices give the same simultaneous quotient
packet, coefficient by coefficient. -/
theorem doubleEdgeJointPacket_association {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    PacketEqv (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)
      (doubleEdgeJointPacketCyclic P₁ Q₁ R₁ P₂ Q₂ R₂) := by
  intro i
  unfold doubleEdgeJointPacket doubleEdgeJointPacketCyclic jointCoeff
    jointCoeffCyclic
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (q_mul_congr (vertexFiber_association P₁ Q₁ R₁ i.val b)
        (vertexFiber_association P₂ Q₂ R₂ i.val b))) (K + 1)

/-- Reversing the endpoints of both shared edges preserves the joint packet.
This is orientation reversal for self-dual SU(2) character labels. -/
theorem doubleEdgeJointPacket_orientation {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    PacketEqv (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)
      (doubleEdgeJointPacket P₂ Q₂ R₂ P₁ Q₁ R₁) := by
  intro i
  unfold doubleEdgeJointPacket jointCoeff
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (Q'.mul_comm_eqv _ _)) (K + 1)

/-- Scalar joint contraction after also applying the physical first-edge
weight.  Together with `jointCoeff`, this is one double sum over the common
pair `(a,b)`. -/
def doubleEdgeJointGram {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) : Q' :=
  fsum (fun a => packetEigen a *
    jointCoeff P₁ Q₁ R₁ P₂ Q₂ R₂ a) (K + 1)

theorem doubleEdgeJointGram_common_pair {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    doubleEdgeJointGram P₁ Q₁ R₁ P₂ Q₂ R₂ ≈
      fsum (fun a => fsum (fun b =>
        (packetEigen a * packetEigen b) *
          (vertexFiber P₁ Q₁ R₁ a b *
            vertexFiber P₂ Q₂ R₂ a b)) (K + 1)) (K + 1) := by
  unfold doubleEdgeJointGram jointCoeff
  exact fsum_eqv_congr _ _ (fun a => by
    refine Q'.eqv_trans _
      (fsum (fun b => packetEigen a *
        (packetEigen b *
          (vertexFiber P₁ Q₁ R₁ a b *
            vertexFiber P₂ Q₂ R₂ a b))) (K + 1)) _ ?_ ?_
    · exact
        (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
          (packetEigen a)
          (fun b => packetEigen b *
            (vertexFiber P₁ Q₁ R₁ a b *
              vertexFiber P₂ Q₂ R₂ a b)) (K + 1))
    · exact fsum_eqv_congr _ _ (fun b =>
        Q'.eqv_symm (Q'.mul_assoc_eqv (packetEigen a) (packetEigen b) _))
        (K + 1)) (K + 1)

/-! ## Padding coherence of the joint quotient -/

private theorem vertexFiber_pad {K L : Nat} (hKL : K ≤ L)
    (P Q R : CharacterPacket K) (a b : Nat) :
    vertexFiber (padPacket hKL P) (padPacket hKL Q) (padPacket hKL R) a b ≈
      vertexFiber P Q R a b := by
  unfold vertexFiber
  simp only [coeffAt_padPacket]
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    (fsum (fun c => fusionInd a b c * coeffAt R c) (K + 1)) _
    (fsum_zero_extension (by omega) ?_) (Q'.eqv_refl _)
  intro c hc
  rw [coeffAt_of_gt R (by omega)]
  exact Q'.mul_zero_eqv _

private theorem vertexFiber_zero_first_above {K : Nat}
    (P Q R : CharacterPacket K) {a : Nat} (ha : K < a) (b : Nat) :
    vertexFiber P Q R a b ≈ 0 := by
  unfold vertexFiber
  rw [coeffAt_of_gt P ha]
  exact Q'.eqv_trans _ (0 * _) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
    (Q'.zero_mul_eqv _)

private theorem vertexFiber_zero_second_above {K : Nat}
    (P Q R : CharacterPacket K) (a : Nat) {b : Nat} (hb : K < b) :
    vertexFiber P Q R a b ≈ 0 := by
  unfold vertexFiber
  rw [coeffAt_of_gt Q hb]
  exact Q'.eqv_trans _ (0 * _) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
    (Q'.zero_mul_eqv _)

private theorem jointCoeff_pad {K L : Nat} (hKL : K ≤ L)
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) (a : Nat) :
    jointCoeff (padPacket hKL P₁) (padPacket hKL Q₁) (padPacket hKL R₁)
        (padPacket hKL P₂) (padPacket hKL Q₂) (padPacket hKL R₂) a ≈
      jointCoeff P₁ Q₁ R₁ P₂ Q₂ R₂ a := by
  unfold jointCoeff
  refine Q'.eqv_trans _
    (fsum (fun b => packetEigen b *
      (vertexFiber P₁ Q₁ R₁ a b * vertexFiber P₂ Q₂ R₂ a b))
      (L + 1)) _ ?_ ?_
  · exact fsum_eqv_congr _ _ (fun b =>
      Q'.mul_eqv_congr_left (packetEigen b) _ _
        (q_mul_congr (vertexFiber_pad hKL P₁ Q₁ R₁ a b)
          (vertexFiber_pad hKL P₂ Q₂ R₂ a b))) (L + 1)
  · exact fsum_zero_extension (by omega) (fun b hb => by
      have hbK : K < b := by omega
      have hzero := vertexFiber_zero_second_above P₁ Q₁ R₁ a hbK
      exact Q'.eqv_trans _ (packetEigen b * (0 * _)) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hzero))
        (Q'.eqv_trans _ (packetEigen b * 0) _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
          (Q'.mul_zero_eqv _)))

private theorem jointCoeff_zero_above {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K)
    {a : Nat} (ha : K < a) :
    jointCoeff P₁ Q₁ R₁ P₂ Q₂ R₂ a ≈ 0 := by
  unfold jointCoeff
  apply YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
  intro b hb
  have hzero := vertexFiber_zero_first_above P₁ Q₁ R₁ ha b
  exact Q'.eqv_trans _ (packetEigen b * (0 * _)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hzero))
    (Q'.eqv_trans _ (packetEigen b * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
      (Q'.mul_zero_eqv _))

/-- Simultaneous padding of all six incident packets pads the joint quotient
packet and adds no spurious shared-label channel. -/
theorem doubleEdgeJointPacket_pad {K L : Nat} (hKL : K ≤ L)
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    PacketEqv
      (doubleEdgeJointPacket (padPacket hKL P₁) (padPacket hKL Q₁)
        (padPacket hKL R₁) (padPacket hKL P₂) (padPacket hKL Q₂)
        (padPacket hKL R₂))
      (padPacket hKL (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)) := by
  intro i
  change jointCoeff (padPacket hKL P₁) (padPacket hKL Q₁) (padPacket hKL R₁)
      (padPacket hKL P₂) (padPacket hKL Q₂) (padPacket hKL R₂) i.val ≈
    coeffAt (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂) i.val
  refine Q'.eqv_trans _
    (jointCoeff P₁ Q₁ R₁ P₂ Q₂ R₂ i.val) _
    (jointCoeff_pad hKL P₁ Q₁ R₁ P₂ Q₂ R₂ i.val) ?_
  by_cases hi : i.val < K + 1
  · rw [coeffAt_of_lt _ hi]
    exact Q'.eqv_refl _
  · rw [coeffAt_of_gt _ (by omega)]
    exact jointCoeff_zero_above P₁ Q₁ R₁ P₂ Q₂ R₂ (by omega)

/-! ## Six genuinely independent input cutoffs -/

private theorem vertexFiber_congr {K : Nat}
    {P P' Q Qalt R R' : CharacterPacket K}
    (hP : PacketEqv P P') (hQ : PacketEqv Q Qalt)
    (hR : PacketEqv R R') (a b : Nat) :
    vertexFiber P Q R a b ≈ vertexFiber P' Qalt R' a b := by
  unfold vertexFiber
  exact q_mul_congr
    (q_mul_congr (coeffAt_packetEqv hP a) (coeffAt_packetEqv hQ b))
    (fsum_eqv_congr _ _ (fun c =>
      Q'.mul_eqv_congr_left (fusionInd a b c) _ _
        (coeffAt_packetEqv hR c)) (K + 1))

private theorem doubleEdgeJointPacket_congr {K : Nat}
    {P₁ P₁' Q₁ Q₁' R₁ R₁' P₂ P₂' Q₂ Q₂' R₂ R₂' :
      CharacterPacket K}
    (hP₁ : PacketEqv P₁ P₁') (hQ₁ : PacketEqv Q₁ Q₁')
    (hR₁ : PacketEqv R₁ R₁') (hP₂ : PacketEqv P₂ P₂')
    (hQ₂ : PacketEqv Q₂ Q₂') (hR₂ : PacketEqv R₂ R₂') :
    PacketEqv (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)
      (doubleEdgeJointPacket P₁' Q₁' R₁' P₂' Q₂' R₂') := by
  intro i
  unfold doubleEdgeJointPacket jointCoeff
  exact fsum_eqv_congr _ _ (fun b =>
    Q'.mul_eqv_congr_left (packetEigen b) _ _
      (q_mul_congr
        (vertexFiber_congr hP₁ hQ₁ hR₁ i.val b)
        (vertexFiber_congr hP₂ hQ₂ hR₂ i.val b))) (K + 1)

def doubleEdgeCutoff
    (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) : Nat :=
  Nat.max N₁ (Nat.max M₁ (Nat.max L₁ (Nat.max N₂ (Nat.max M₂ L₂))))

private theorem de_le₁ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    N₁ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_max_left _ _

private theorem de_le₂ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    M₁ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem de_le₃ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    L₁ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

private theorem de_le₄ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    N₂ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

private theorem de_le₅ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    M₂ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))

private theorem de_le₆ (N₁ M₁ L₁ N₂ M₂ L₂ : Nat) :
    L₂ ≤ doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ :=
  Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))

def padDE₁ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (P : CharacterPacket N₁) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₁ N₁ M₁ L₁ N₂ M₂ L₂) P

def padDE₂ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (Q : CharacterPacket M₁) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₂ N₁ M₁ L₁ N₂ M₂ L₂) Q

def padDE₃ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (R : CharacterPacket L₁) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₃ N₁ M₁ L₁ N₂ M₂ L₂) R

def padDE₄ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (P : CharacterPacket N₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₄ N₁ M₁ L₁ N₂ M₂ L₂) P

def padDE₅ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (Q : CharacterPacket M₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₅ N₁ M₁ L₁ N₂ M₂ L₂) Q

def padDE₆ {N₁ M₁ L₁ N₂ M₂ L₂ : Nat} (R : CharacterPacket L₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  padPacket (de_le₆ N₁ M₁ L₁ N₂ M₂ L₂) R

def arbitraryDoubleEdgeJointPacket
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  doubleEdgeJointPacket (padDE₁ (M₁ := M₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) P₁)
    (padDE₂ (N₁ := N₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) Q₁)
    (padDE₃ (N₁ := N₁) (M₁ := M₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) R₁)
    (padDE₄ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (M₂ := M₂) (L₂ := L₂) P₂)
    (padDE₅ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (L₂ := L₂) Q₂)
    (padDE₆ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (M₂ := M₂) R₂)

private theorem doubleEdgeCutoff_mono
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂') :
    doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂ ≤
      doubleEdgeCutoff N₁' M₁' L₁' N₂' M₂' L₂' := by
  unfold doubleEdgeCutoff
  apply (Nat.max_le).2
  constructor
  · exact Nat.le_trans hN₁ (Nat.le_max_left _ _)
  · apply (Nat.max_le).2
    constructor
    · exact Nat.le_trans hM₁
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    · apply (Nat.max_le).2
      constructor
      · exact Nat.le_trans hL₁
          (Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
      · apply (Nat.max_le).2
        constructor
        · exact Nat.le_trans hN₂
            (Nat.le_trans (Nat.le_max_left _ _)
              (Nat.le_trans (Nat.le_max_right _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
        · apply (Nat.max_le).2
          exact ⟨Nat.le_trans hM₂
              (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_trans (Nat.le_max_right _ _)
                  (Nat.le_trans (Nat.le_max_right _ _)
                    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))),
            Nat.le_trans hL₂
              (Nat.le_trans (Nat.le_max_right _ _)
                (Nat.le_trans (Nat.le_max_right _ _)
                  (Nat.le_trans (Nat.le_max_right _ _)
                    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))))⟩

/-- Six unrelated cutoff enlargements agree with padding the already-formed
simultaneous joint quotient. -/
theorem arbitraryDoubleEdgeJointPacket_pad_independent
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    PacketEqv
      (arbitraryDoubleEdgeJointPacket (padPacket hN₁ P₁) (padPacket hM₁ Q₁)
        (padPacket hL₁ R₁) (padPacket hN₂ P₂) (padPacket hM₂ Q₂)
        (padPacket hL₂ R₂))
      (padPacket (doubleEdgeCutoff_mono hN₁ hM₁ hL₁ hN₂ hM₂ hL₂)
        (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)) := by
  let K := doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂
  let K' := doubleEdgeCutoff N₁' M₁' L₁' N₂' M₂' L₂'
  have hKK : K ≤ K' :=
    doubleEdgeCutoff_mono hN₁ hM₁ hL₁ hN₂ hM₂ hL₂
  let A₁ : CharacterPacket K := padDE₁ (M₁ := M₁) (L₁ := L₁)
    (N₂ := N₂) (M₂ := M₂) (L₂ := L₂) P₁
  let B₁ : CharacterPacket K := padDE₂ (N₁ := N₁) (L₁ := L₁)
    (N₂ := N₂) (M₂ := M₂) (L₂ := L₂) Q₁
  let C₁ : CharacterPacket K := padDE₃ (N₁ := N₁) (M₁ := M₁)
    (N₂ := N₂) (M₂ := M₂) (L₂ := L₂) R₁
  let A₂ : CharacterPacket K := padDE₄ (N₁ := N₁) (M₁ := M₁)
    (L₁ := L₁) (M₂ := M₂) (L₂ := L₂) P₂
  let B₂ : CharacterPacket K := padDE₅ (N₁ := N₁) (M₁ := M₁)
    (L₁ := L₁) (N₂ := N₂) (L₂ := L₂) Q₂
  let C₂ : CharacterPacket K := padDE₆ (N₁ := N₁) (M₁ := M₁)
    (L₁ := L₁) (N₂ := N₂) (M₂ := M₂) R₂
  let A₁' : CharacterPacket K' := padDE₁ (M₁ := M₁') (L₁ := L₁')
    (N₂ := N₂') (M₂ := M₂') (L₂ := L₂') (padPacket hN₁ P₁)
  let B₁' : CharacterPacket K' := padDE₂ (N₁ := N₁') (L₁ := L₁')
    (N₂ := N₂') (M₂ := M₂') (L₂ := L₂') (padPacket hM₁ Q₁)
  let C₁' : CharacterPacket K' := padDE₃ (N₁ := N₁') (M₁ := M₁')
    (N₂ := N₂') (M₂ := M₂') (L₂ := L₂') (padPacket hL₁ R₁)
  let A₂' : CharacterPacket K' := padDE₄ (N₁ := N₁') (M₁ := M₁')
    (L₁ := L₁') (M₂ := M₂') (L₂ := L₂') (padPacket hN₂ P₂)
  let B₂' : CharacterPacket K' := padDE₅ (N₁ := N₁') (M₁ := M₁')
    (L₁ := L₁') (N₂ := N₂') (L₂ := L₂') (padPacket hM₂ Q₂)
  let C₂' : CharacterPacket K' := padDE₆ (N₁ := N₁') (M₁ := M₁')
    (L₁ := L₁') (N₂ := N₂') (M₂ := M₂') (padPacket hL₂ R₂)
  have hA₁ : PacketEqv A₁' (padPacket hKK A₁) := by
    intro i; change coeffAt (padPacket hN₁ P₁) i.val ≈ coeffAt A₁ i.val
    simp only [A₁, padDE₁, coeffAt_padPacket]; exact Q'.eqv_refl _
  have hB₁ : PacketEqv B₁' (padPacket hKK B₁) := by
    intro i; change coeffAt (padPacket hM₁ Q₁) i.val ≈ coeffAt B₁ i.val
    simp only [B₁, padDE₂, coeffAt_padPacket]; exact Q'.eqv_refl _
  have hC₁ : PacketEqv C₁' (padPacket hKK C₁) := by
    intro i; change coeffAt (padPacket hL₁ R₁) i.val ≈ coeffAt C₁ i.val
    simp only [C₁, padDE₃, coeffAt_padPacket]; exact Q'.eqv_refl _
  have hA₂ : PacketEqv A₂' (padPacket hKK A₂) := by
    intro i; change coeffAt (padPacket hN₂ P₂) i.val ≈ coeffAt A₂ i.val
    simp only [A₂, padDE₄, coeffAt_padPacket]; exact Q'.eqv_refl _
  have hB₂ : PacketEqv B₂' (padPacket hKK B₂) := by
    intro i; change coeffAt (padPacket hM₂ Q₂) i.val ≈ coeffAt B₂ i.val
    simp only [B₂, padDE₅, coeffAt_padPacket]; exact Q'.eqv_refl _
  have hC₂ : PacketEqv C₂' (padPacket hKK C₂) := by
    intro i; change coeffAt (padPacket hL₂ R₂) i.val ≈ coeffAt C₂ i.val
    simp only [C₂, padDE₆, coeffAt_padPacket]; exact Q'.eqv_refl _
  change PacketEqv (doubleEdgeJointPacket A₁' B₁' C₁' A₂' B₂' C₂')
    (padPacket hKK (doubleEdgeJointPacket A₁ B₁ C₁ A₂ B₂ C₂))
  exact packetEqv_trans
    (doubleEdgeJointPacket_congr hA₁ hB₁ hC₁ hA₂ hB₂ hC₂)
    (doubleEdgeJointPacket_pad hKK A₁ B₁ C₁ A₂ B₂ C₂)

/-- The cyclic presentation of the simultaneous quotient at the canonical
maximum of six unrelated input cutoffs. -/
def arbitraryDoubleEdgeJointPacketCyclic
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  doubleEdgeJointPacketCyclic
    (padDE₁ (M₁ := M₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) P₁)
    (padDE₂ (N₁ := N₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) Q₁)
    (padDE₃ (N₁ := N₁) (M₁ := M₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) R₁)
    (padDE₄ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (M₂ := M₂) (L₂ := L₂) P₂)
    (padDE₅ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (L₂ := L₂) Q₂)
    (padDE₆ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (M₂ := M₂) R₂)

/-- Endpoint reversal written at the original canonical cutoff.  Keeping the
same carrier avoids identifying definitionally different nestings of `max`. -/
def arbitraryDoubleEdgeOrientationReverse
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    CharacterPacket (doubleEdgeCutoff N₁ M₁ L₁ N₂ M₂ L₂) :=
  doubleEdgeJointPacket
    (padDE₄ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (M₂ := M₂) (L₂ := L₂) P₂)
    (padDE₅ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (L₂ := L₂) Q₂)
    (padDE₆ (N₁ := N₁) (M₁ := M₁) (L₁ := L₁)
      (N₂ := N₂) (M₂ := M₂) R₂)
    (padDE₁ (M₁ := M₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) P₁)
    (padDE₂ (N₁ := N₁) (L₁ := L₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) Q₁)
    (padDE₃ (N₁ := N₁) (M₁ := M₁) (N₂ := N₂)
      (M₂ := M₂) (L₂ := L₂) R₁)

theorem arbitraryDoubleEdgeJointPacket_association
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    PacketEqv (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)
      (arbitraryDoubleEdgeJointPacketCyclic P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  doubleEdgeJointPacket_association _ _ _ _ _ _

theorem arbitraryDoubleEdgeJointPacket_orientation
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    PacketEqv (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)
      (arbitraryDoubleEdgeOrientationReverse P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  doubleEdgeJointPacket_orientation _ _ _ _ _ _

/-! ## Exact independent-edge counterexample -/

def doubleEdgeFundamental : CharacterPacket 1 := trivalentFundamentalLeg

def fundamentalSequentialIndependentGram : Q' :=
  packetWilsonGram doubleEdgeFundamental doubleEdgeFundamental *
    packetWilsonGram doubleEdgeFundamental doubleEdgeFundamental

def fundamentalSimultaneousDoubleEdgeGram : Q' :=
  doubleEdgeJointGram doubleEdgeFundamental doubleEdgeFundamental
    doubleEdgeFundamental doubleEdgeFundamental doubleEdgeFundamental
    doubleEdgeFundamental

theorem fundamental_sequential_independent_exact :
    fundamentalSequentialIndependentGram ≈ Q'.mkPos 1 64 (by decide) := by decide

theorem fundamental_simultaneous_joint_zero :
    fundamentalSimultaneousDoubleEdgeGram ≈ 0 := by decide

/-- **Banked simultaneous-constraint fence.**  Sequential independent edge
elimination disagrees with the true two-vertex intertwiner quotient. -/
theorem fundamental_sequential_joint_disagree :
    ¬ (fundamentalSequentialIndependentGram ≈
      fundamentalSimultaneousDoubleEdgeGram) := by decide

/-! ## Completion and physical transfer descent -/

def completedDoubleEdgeJointState {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂))

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

theorem completedDoubleEdge_association {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    completedDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      embedV packetColimitGNS
        (stagePacket
          (doubleEdgeJointPacketCyclic P₁ Q₁ R₁ P₂ Q₂ R₂)) :=
  embedV_eq_of_packetEqv
    (doubleEdgeJointPacket_association P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedDoubleEdge_orientation {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    completedDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      completedDoubleEdgeJointState P₂ Q₂ R₂ P₁ Q₁ R₁ :=
  embedV_eq_of_packetEqv
    (doubleEdgeJointPacket_orientation P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedDoubleEdge_pad {K L : Nat} (hKL : K ≤ L)
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    completedDoubleEdgeJointState (padPacket hKL P₁) (padPacket hKL Q₁)
        (padPacket hKL R₁) (padPacket hKL P₂) (padPacket hKL Q₂)
        (padPacket hKL R₂) =
      completedDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ := by
  refine Eq.trans (embedV_eq_of_packetEqv
    (doubleEdgeJointPacket_pad hKL P₁ Q₁ R₁ P₂ Q₂ R₂)) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => by
      change coeffAt
        (padPacket hKL
          (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)) s ≈
        coeffAt (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂) s
      rw [coeffAt_padPacket]
      exact Q'.eqv_refl _))

theorem completedDoubleEdge_transfer_exact {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    completedPacketTransfer
        (completedDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer
          (doubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂))) :=
  completedPacketTransfer_embed _

theorem completedDoubleEdge_transfer_association_descends {K : Nat}
    (P₁ Q₁ R₁ P₂ Q₂ R₂ : CharacterPacket K) :
    completedPacketTransfer
        (completedDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedPacketTransfer
        (embedV packetColimitGNS
          (stagePacket
            (doubleEdgeJointPacketCyclic P₁ Q₁ R₁ P₂ Q₂ R₂))) :=
  congrArg completedPacketTransfer
    (completedDoubleEdge_association P₁ Q₁ R₁ P₂ Q₂ R₂)

/-! ## Six-cutoff completion and transfer descent -/

def completedArbitraryDoubleEdgeJointState
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂))

def completedArbitraryDoubleEdgeCyclicState
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket
      (arbitraryDoubleEdgeJointPacketCyclic P₁ Q₁ R₁ P₂ Q₂ R₂))

def completedArbitraryDoubleEdgeOrientationReverseState
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS
    (stagePacket
      (arbitraryDoubleEdgeOrientationReverse P₁ Q₁ R₁ P₂ Q₂ R₂))

theorem completedArbitraryDoubleEdge_association
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      completedArbitraryDoubleEdgeCyclicState P₁ Q₁ R₁ P₂ Q₂ R₂ :=
  embedV_eq_of_packetEqv
    (arbitraryDoubleEdgeJointPacket_association P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedArbitraryDoubleEdge_orientation
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      completedArbitraryDoubleEdgeOrientationReverseState
        P₁ Q₁ R₁ P₂ Q₂ R₂ :=
  embedV_eq_of_packetEqv
    (arbitraryDoubleEdgeJointPacket_orientation P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedArbitraryDoubleEdge_pad_independent
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeJointState
        (padPacket hN₁ P₁) (padPacket hM₁ Q₁) (padPacket hL₁ R₁)
        (padPacket hN₂ P₂) (padPacket hM₂ Q₂) (padPacket hL₂ R₂) =
      completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂ := by
  refine Eq.trans (embedV_eq_of_packetEqv
    (arbitraryDoubleEdgeJointPacket_pad_independent
      hN₁ hM₁ hL₁ hN₂ hM₂ hL₂ P₁ Q₁ R₁ P₂ Q₂ R₂)) ?_
  exact embedV_stage_pad_eq
    (doubleEdgeCutoff_mono hN₁ hM₁ hL₁ hN₂ hM₂ hL₂)
    (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedArbitraryDoubleEdge_transfer_exact
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedPacketTransfer
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      embedV packetColimitGNS
        (stagePacket (packetTransfer
          (arbitraryDoubleEdgeJointPacket P₁ Q₁ R₁ P₂ Q₂ R₂))) :=
  completedPacketTransfer_embed _

theorem completedArbitraryDoubleEdge_transfer_association_descends
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedPacketTransfer
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedPacketTransfer
        (completedArbitraryDoubleEdgeCyclicState P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  congrArg completedPacketTransfer
    (completedArbitraryDoubleEdge_association P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedArbitraryDoubleEdge_transfer_orientation_descends
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedPacketTransfer
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedPacketTransfer
        (completedArbitraryDoubleEdgeOrientationReverseState
          P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  congrArg completedPacketTransfer
    (completedArbitraryDoubleEdge_orientation P₁ Q₁ R₁ P₂ Q₂ R₂)

theorem completedArbitraryDoubleEdge_transfer_pad_descends
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedPacketTransfer
        (completedArbitraryDoubleEdgeJointState
          (padPacket hN₁ P₁) (padPacket hM₁ Q₁) (padPacket hL₁ R₁)
          (padPacket hN₂ P₂) (padPacket hM₂ Q₂) (padPacket hL₂ R₂)) =
      completedPacketTransfer
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  congrArg completedPacketTransfer
    (completedArbitraryDoubleEdge_pad_independent
      hN₁ hM₁ hL₁ hN₂ hM₂ hL₂ P₁ Q₁ R₁ P₂ Q₂ R₂)

end YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient

#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.vertexFiber_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.doubleEdgeJointPacket_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.doubleEdgeJointPacket_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.doubleEdgeJointGram_common_pair
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.doubleEdgeJointPacket_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.arbitraryDoubleEdgeJointPacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.arbitraryDoubleEdgeJointPacket_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.arbitraryDoubleEdgeJointPacket_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.fundamental_sequential_independent_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.fundamental_simultaneous_joint_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.fundamental_sequential_joint_disagree
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedDoubleEdge_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedDoubleEdge_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedDoubleEdge_pad
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedDoubleEdge_transfer_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedDoubleEdge_transfer_association_descends
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_transfer_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_transfer_association_descends
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_transfer_orientation_descends
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient.completedArbitraryDoubleEdge_transfer_pad_descends
