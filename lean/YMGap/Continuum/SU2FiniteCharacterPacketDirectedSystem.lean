/-
# Directed compatibility of finite SU(2) character packets

The uniform finite-packet contraction is useful for a limit only when the
finite carriers form a coherent system.  This file supplies the missing exact
cutoff maps.  A packet is padded by its already-defined zero extension;
padding preserves every coefficient, commutes with the physical Wilson
transfer, and preserves the interacting Wilson Gram exactly.  The construction
also restricts to the vacuum-free carriers used by spectral localization.

Consequently the cutoff-independent `1/64` contraction is compatible with the
directed maps, rather than being a family of unrelated finite inequalities.
This remains a one-link character directed system, not the four-dimensional
thermodynamic or continuum limit.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization

namespace YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Zero-padding from cutoff `N` to any larger cutoff `M`.  The proof records
the directed-system orientation; coefficients are supplied by `coeffAt`. -/
def padPacket {N M : Nat} (_hNM : N ≤ M)
    (P : CharacterPacket N) : CharacterPacket M where
  coeff i := coeffAt P i.val

/-- Padding preserves the entire zero-extended coefficient sequence, including
all coordinates above both cutoffs. -/
theorem coeffAt_padPacket {N M : Nat} (hNM : N ≤ M)
    (P : CharacterPacket N) (s : Nat) :
    coeffAt (padPacket hNM P) s = coeffAt P s := by
  unfold coeffAt
  by_cases hsM : s < M + 1
  · rw [dif_pos hsM]
    rfl
  · rw [dif_neg hsM]
    have hsN : ¬ s < N + 1 := by omega
    rw [dif_neg hsN]

/-- Coefficient equivalence can be read on the zero-extended sequence. -/
theorem coeffAt_packetEqv {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketEqv P Q) (s : Nat) : coeffAt P s ≈ coeffAt Q s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt P hs, coeffAt_of_lt Q hs]
    exact hPQ ⟨s, hs⟩
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_refl 0

theorem packetEqv_symm {N : Nat} {P Q : CharacterPacket N}
    (hPQ : PacketEqv P Q) : PacketEqv Q P :=
  fun i => Q'.eqv_symm (hPQ i)

theorem padPacket_refl {N : Nat} (P : CharacterPacket N) :
    PacketEqv (padPacket (Nat.le_refl N) P) P := by
  intro i
  change coeffAt P i.val ≈ P.coeff i
  rw [coeffAt_of_lt P i.isLt]
  exact Q'.eqv_refl _

theorem padPacket_trans {L N M : Nat} (hLN : L ≤ N) (hNM : N ≤ M)
    (P : CharacterPacket L) :
    PacketEqv (padPacket hNM (padPacket hLN P))
      (padPacket (Nat.le_trans hLN hNM) P) := by
  intro i
  change coeffAt (padPacket hLN P) i.val ≈ coeffAt P i.val
  rw [coeffAt_padPacket]
  exact Q'.eqv_refl _

/-- Padding loses no coefficient information. -/
theorem padPacket_injective {N M : Nat} (hNM : N ≤ M)
    {P Q : CharacterPacket N}
    (hpad : PacketEqv (padPacket hNM P) (padPacket hNM Q)) :
    PacketEqv P Q := by
  intro i
  have hiM : i.val < M + 1 := by omega
  have h := hpad ⟨i.val, hiM⟩
  change coeffAt P i.val ≈ coeffAt Q i.val at h
  rw [coeffAt_of_lt P i.isLt, coeffAt_of_lt Q i.isLt] at h
  exact h

/-- The physical same-state transfer commutes with every directed padding
map, coefficient by coefficient. -/
theorem padPacket_transfer {N M : Nat} (hNM : N ≤ M)
    (P : CharacterPacket N) :
    PacketEqv (padPacket hNM (packetTransfer P))
      (packetTransfer (padPacket hNM P)) := by
  intro i
  change coeffAt (packetTransfer P) i.val ≈
    packetEigen i.val * coeffAt P i.val
  exact coeffAt_packetTransfer P i.val

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

/-- The interacting Wilson Gram respects coefficient equivalence at a fixed
cutoff. -/
theorem packetWilsonGram_congr {N : Nat}
    {P P' R R' : CharacterPacket N}
    (hP : PacketEqv P P') (hR : PacketEqv R R') :
    packetWilsonGram P R ≈ packetWilsonGram P' R' := by
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s * (coeffAt P s * coeffAt R s)) (N + 1)) _
    (packetWilsonGram_diagonal P R) ?_
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s * (coeffAt P' s * coeffAt R' s)) (N + 1)) _
    (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (packetEigen s) _ _
        (q_mul_congr
          (coeffAt_packetEqv hP s) (coeffAt_packetEqv hR s))) (N + 1)) ?_
  exact Q'.eqv_symm (packetWilsonGram_diagonal P' R')

/-- Zero-padding is an exact isometry for the interacting Wilson Gram. -/
theorem packetWilsonGram_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    packetWilsonGram (padPacket hNM P) (padPacket hNM Q) ≈
      packetWilsonGram P Q := by
  let term := fun s => packetEigen s * (coeffAt P s * coeffAt Q s)
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt (padPacket hNM P) s * coeffAt (padPacket hNM Q) s))
      (M + 1)) _
    (packetWilsonGram_diagonal (padPacket hNM P) (padPacket hNM Q)) ?_
  refine Q'.eqv_trans _ (fsum term (M + 1)) _ ?_ ?_
  · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun s => by
      rw [coeffAt_padPacket, coeffAt_padPacket]
      exact Q'.eqv_refl _) (M + 1)
  · refine Q'.eqv_trans _ (fsum term (N + 1)) _
      (fsum_zero_extension (by omega) ?_) ?_
    · intro s hs
      have hsP : coeffAt P s = 0 := coeffAt_of_gt P (by omega)
      have hsQ : coeffAt Q s = 0 := coeffAt_of_gt Q (by omega)
      dsimp [term]
      rw [hsP, hsQ]
      exact Q'.eqv_trans _ (packetEigen s * 0) _
        (Q'.mul_eqv_congr_left (packetEigen s) _ _ (q_zero_mul 0))
        (Q'.mul_zero_eqv _)
    · exact Q'.eqv_symm (packetWilsonGram_diagonal P Q)

/-- The transferred Gram is likewise unchanged along a cutoff inclusion. -/
theorem packetTransferredGram_pad {N M : Nat} (hNM : N ≤ M)
    (P Q : CharacterPacket N) :
    packetWilsonGram
        (packetTransfer (padPacket hNM P))
        (packetTransfer (padPacket hNM Q)) ≈
      packetWilsonGram (packetTransfer P) (packetTransfer Q) := by
  refine Q'.eqv_trans _
    (packetWilsonGram
      (padPacket hNM (packetTransfer P))
      (padPacket hNM (packetTransfer Q))) _ ?_ ?_
  · exact packetWilsonGram_congr
      (packetEqv_symm (padPacket_transfer hNM P))
      (packetEqv_symm (padPacket_transfer hNM Q))
  · exact packetWilsonGram_pad hNM (packetTransfer P) (packetTransfer Q)

/-! ## Vacuum-free directed subsystem -/

def padVacuumFree {N M : Nat} (hNM : N ≤ M)
    (P : VacuumFreePacket N) : VacuumFreePacket M where
  packet := padPacket hNM P.packet
  vacuum_zero := by
    rw [coeffAt_padPacket]
    exact P.vacuum_zero

theorem padVacuumFree_transfer {N M : Nat} (hNM : N ≤ M)
    (P : VacuumFreePacket N) :
    VacuumFreeEqv (padVacuumFree hNM (vacuumFreeTransfer P))
      (vacuumFreeTransfer (padVacuumFree hNM P)) :=
  padPacket_transfer hNM P.packet

/-- The exact cutoff-independent contraction applies on every padded carrier.
Together with the two Gram-isometry theorems above, this is a coherent
directed family of estimates. -/
theorem padded_vacuumfree_uniform_contraction {N M : Nat}
    (hNM : N ≤ M) (P : VacuumFreePacket N) :
    packetWilsonGram
        (packetTransfer (padPacket hNM P.packet))
        (packetTransfer (padPacket hNM P.packet)) ≤
      (SU2PeterWeylWilsonBlock.eighth *
          SU2PeterWeylWilsonBlock.eighth) *
        packetWilsonGram (padPacket hNM P.packet) (padPacket hNM P.packet) :=
  vacuumfree_packet_uniform_contraction (padPacket hNM P.packet) (by
    rw [coeffAt_padPacket]
    exact P.vacuum_zero)

end YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.coeffAt_padPacket
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.padPacket_transfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.packetWilsonGram_pad
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.packetTransferredGram_pad
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.padVacuumFree_transfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem.padded_vacuumfree_uniform_contraction
