/-
# Constructive vacuum projection on the completed character-packet colimit

The completed packet transfer has an exact `1/8` edge on Cauchy sequences
presented by vacuum-free representatives.  Here that presentation is produced
canonically: delete the trivial-character coefficient at every finite stage.
The deletion is cutoff-coherent, rational-linear, contractive, idempotent, and
commutes with the physical transfer, so it descends to the explicit GNS
completion.  Consequently every completed vector has a canonical excited
projection on which the exact edge estimate applies.

Honest scope: this is the all-character one-link sector.  The construction does
not identify its projection with the orthogonal complement inside an
overlapping four-dimensional finite-volume network.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer

namespace YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, zero_num_cast, zero_den_cast, one_num_cast,
               one_den_cast, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem fsum_le_fsum {f g : Nat → Q'}
    (h : ∀ s, f s ≤ g s) : ∀ N, fsum f N ≤ fsum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => Q'.add_le_add (fsum_le_fsum h N) (h N)

private theorem fsum_eqv_zero {f : Nat → Q'}
    (h : ∀ s, f s ≈ 0) : ∀ N, fsum f N ≈ 0
  | 0 => Q'.eqv_refl 0
  | N + 1 =>
      Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (fsum_eqv_zero h N) (h N))
        (q_zero_add_eqv 0)

/-! ## The exact finite-stage projection -/

/-- Delete only the trivial-character coefficient. -/
def stagedRemoveVacuum (A : StagedPacket) : StagedPacket :=
  { cutoff := A.cutoff
    packet :=
      { coeff := fun i => if i.val = 0 then 0 else A.packet.coeff i } }

theorem coeffAt_stagedRemoveVacuum (A : StagedPacket) (s : Nat) :
    coeffAt (stagedRemoveVacuum A).packet s ≈
      if s = 0 then 0 else coeffAt A.packet s := by
  by_cases hs0 : s = 0
  · subst s
    rw [coeffAt_of_lt (stagedRemoveVacuum A).packet (by omega)]
    simp [stagedRemoveVacuum]
    exact Q'.eqv_refl 0
  · by_cases hs : s < A.cutoff + 1
    · rw [coeffAt_of_lt (stagedRemoveVacuum A).packet hs,
        coeffAt_of_lt A.packet hs]
      simp [stagedRemoveVacuum, hs0]
      exact Q'.eqv_refl _
    · unfold coeffAt
      simp only [stagedRemoveVacuum, hs, hs0, if_false]
      exact Q'.eqv_refl 0

theorem stagedRemoveVacuum_congr {A B : StagedPacket}
    (hAB : StagedEqv A B) :
    StagedEqv (stagedRemoveVacuum A) (stagedRemoveVacuum B) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum A s) ?_
    exact Q'.eqv_symm (by
      simpa [hs] using coeffAt_stagedRemoveVacuum B s)
  · refine Q'.eqv_trans _ (coeffAt A.packet s) _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum A s) ?_
    exact Q'.eqv_trans _ (coeffAt B.packet s) _ (hAB s)
      (Q'.eqv_symm (by
        simpa [hs] using coeffAt_stagedRemoveVacuum B s))

theorem stagedRemoveVacuum_vacuumFree (A : StagedPacket) :
    StagedVacuumFree (stagedRemoveVacuum A) := by
  simpa [StagedVacuumFree] using coeffAt_stagedRemoveVacuum A 0

theorem stagedRemoveVacuum_add (A B : StagedPacket) :
    StagedEqv (stagedRemoveVacuum (stagedAdd A B))
      (stagedAdd (stagedRemoveVacuum A) (stagedRemoveVacuum B)) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedAdd A B) s) ?_
    refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
    · exact Q'.eqv_symm (q_zero_add_eqv 0)
    · refine Q'.eqv_trans _
        (coeffAt (stagedRemoveVacuum A).packet s +
          coeffAt (stagedRemoveVacuum B).packet s) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_symm (by
            simpa [hs] using coeffAt_stagedRemoveVacuum A s))
          (Q'.eqv_symm (by
            simpa [hs] using coeffAt_stagedRemoveVacuum B s))
      · exact Q'.eqv_symm
          (coeffAt_stagedAdd (stagedRemoveVacuum A)
            (stagedRemoveVacuum B) s)
  · refine Q'.eqv_trans _ (coeffAt (stagedAdd A B).packet s) _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedAdd A B) s) ?_
    refine Q'.eqv_trans _
      (coeffAt A.packet s + coeffAt B.packet s) _
      (coeffAt_stagedAdd A B s) ?_
    refine Q'.eqv_trans _
      (coeffAt (stagedRemoveVacuum A).packet s +
        coeffAt (stagedRemoveVacuum B).packet s) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum B s))
    · exact Q'.eqv_symm
        (coeffAt_stagedAdd (stagedRemoveVacuum A)
          (stagedRemoveVacuum B) s)

theorem stagedRemoveVacuum_smul (q : Q') (A : StagedPacket) :
    StagedEqv (stagedRemoveVacuum (stagedSmul q A))
      (stagedSmul q (stagedRemoveVacuum A)) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedSmul q A) s) ?_
    refine Q'.eqv_trans _ (q * 0) _
      (Q'.eqv_symm (Q'.mul_zero_eqv q)) ?_
    refine Q'.eqv_trans _
      (q * coeffAt (stagedRemoveVacuum A).packet s) _
      (Q'.mul_eqv_congr_left q _ _
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))) ?_
    exact Q'.eqv_symm
      (coeffAt_stagedSmul q (stagedRemoveVacuum A) s)
  · refine Q'.eqv_trans _ (coeffAt (stagedSmul q A).packet s) _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedSmul q A) s) ?_
    refine Q'.eqv_trans _ (q * coeffAt A.packet s) _
      (coeffAt_stagedSmul q A s) ?_
    refine Q'.eqv_trans _
      (q * coeffAt (stagedRemoveVacuum A).packet s) _
      (Q'.mul_eqv_congr_left q _ _
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))) ?_
    exact Q'.eqv_symm
      (coeffAt_stagedSmul q (stagedRemoveVacuum A) s)

theorem stagedRemoveVacuum_neg (A : StagedPacket) :
    StagedEqv (stagedRemoveVacuum (stagedNeg A))
      (stagedNeg (stagedRemoveVacuum A)) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedNeg A) s) ?_
    refine Q'.eqv_trans _ (-(0 : Q')) _ (by decide) ?_
    refine Q'.eqv_trans _
      (-(coeffAt (stagedRemoveVacuum A).packet s)) _
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))) ?_
    exact Q'.eqv_symm (coeffAt_stagedNeg (stagedRemoveVacuum A) s)
  · refine Q'.eqv_trans _ (coeffAt (stagedNeg A).packet s) _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum (stagedNeg A) s) ?_
    refine Q'.eqv_trans _ (-(coeffAt A.packet s)) _
      (coeffAt_stagedNeg A s) ?_
    refine Q'.eqv_trans _
      (-(coeffAt (stagedRemoveVacuum A).packet s)) _
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))) ?_
    exact Q'.eqv_symm (coeffAt_stagedNeg (stagedRemoveVacuum A) s)

theorem stagedRemoveVacuum_sub (A B : StagedPacket) :
    StagedEqv
      (stagedRemoveVacuum (packetColimitGNS.sub A B))
      (packetColimitGNS.sub (stagedRemoveVacuum A)
        (stagedRemoveVacuum B)) := by
  exact stagedEqv_trans (stagedRemoveVacuum_add A (stagedNeg B))
    (stagedAdd_congr (stagedEqv_refl _)
      (stagedRemoveVacuum_neg B))

theorem stagedRemoveVacuum_idempotent (A : StagedPacket) :
    StagedEqv (stagedRemoveVacuum (stagedRemoveVacuum A))
      (stagedRemoveVacuum A) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using
        coeffAt_stagedRemoveVacuum (stagedRemoveVacuum A) s) ?_
    exact Q'.eqv_symm (by
      simpa [hs] using coeffAt_stagedRemoveVacuum A s)
  · refine Q'.eqv_trans _
      (coeffAt (stagedRemoveVacuum A).packet s) _ (by
        simpa [hs] using
          coeffAt_stagedRemoveVacuum (stagedRemoveVacuum A) s) ?_
    exact Q'.eqv_refl _

theorem stagedRemoveVacuum_transfer_commute (A : StagedPacket) :
    StagedEqv
      (stagedTransfer (stagedRemoveVacuum A))
      (stagedRemoveVacuum (stagedTransfer A)) := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _
      (packetEigen s * coeffAt (stagedRemoveVacuum A).packet s) _
      (coeffAt_packetTransfer (stagedRemoveVacuum A).packet s) ?_
    refine Q'.eqv_trans _ (packetEigen s * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (by
        simpa [hs] using coeffAt_stagedRemoveVacuum A s)) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
    exact Q'.eqv_symm (by
      simpa [hs] using
        coeffAt_stagedRemoveVacuum (stagedTransfer A) s)
  · refine Q'.eqv_trans _
      (packetEigen s * coeffAt (stagedRemoveVacuum A).packet s) _
      (coeffAt_packetTransfer (stagedRemoveVacuum A).packet s) ?_
    refine Q'.eqv_trans _
      (packetEigen s * coeffAt A.packet s) _
      (Q'.mul_eqv_congr_left _ _ _ (by
        simpa [hs] using coeffAt_stagedRemoveVacuum A s)) ?_
    refine Q'.eqv_trans _
      (coeffAt (stagedTransfer A).packet s) _
      (Q'.eqv_symm (coeffAt_packetTransfer A.packet s)) ?_
    exact Q'.eqv_symm (by
      simpa [hs] using
        coeffAt_stagedRemoveVacuum (stagedTransfer A) s)

/-! ## Complementary vacuum part -/

/-- The complementary carrier part, defined constructively as `A - P_exc A`. -/
def stagedKeepVacuum (A : StagedPacket) : StagedPacket :=
  packetColimitGNS.sub A (stagedRemoveVacuum A)

theorem coeffAt_stagedKeepVacuum (A : StagedPacket) (s : Nat) :
    coeffAt (stagedKeepVacuum A).packet s ≈
      if s = 0 then coeffAt A.packet s else 0 := by
  refine Q'.eqv_trans _
    (coeffAt A.packet s +
      coeffAt (stagedNeg (stagedRemoveVacuum A)).packet s) _
    (coeffAt_stagedAdd A (stagedNeg (stagedRemoveVacuum A)) s) ?_
  refine Q'.eqv_trans _
    (coeffAt A.packet s +
      -(coeffAt (stagedRemoveVacuum A).packet s)) _
    (Q'.add_eqv_congr_left _ _ _
      (coeffAt_stagedNeg (stagedRemoveVacuum A) s)) ?_
  by_cases hs : s = 0
  · rw [if_pos hs]
    refine Q'.eqv_trans _
      (coeffAt A.packet s + -(0 : Q')) _ ?_ (by ring_qeqv)
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (by
        simpa [hs] using coeffAt_stagedRemoveVacuum A s))
  · rw [if_neg hs]
    refine Q'.eqv_trans _
      (coeffAt A.packet s + -(coeffAt A.packet s)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))
    · exact q_add_neg_self _

theorem stagedKeepVacuum_fixed (A : StagedPacket) :
    StagedEqv (stagedTransfer (stagedKeepVacuum A))
      (stagedKeepVacuum A) := by
  intro s
  refine Q'.eqv_trans _
    (packetEigen s * coeffAt (stagedKeepVacuum A).packet s) _
    (coeffAt_packetTransfer (stagedKeepVacuum A).packet s) ?_
  by_cases hs : s = 0
  · subst s
    rw [packetEigen_zero]
    exact Q'.one_mul_eqv _
  · refine Q'.eqv_trans _ (packetEigen s * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (by
        simpa [hs] using coeffAt_stagedKeepVacuum A s)) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) ?_
    exact Q'.eqv_symm (by
      simpa [hs] using coeffAt_stagedKeepVacuum A s)

theorem stagedKeep_add_remove (A : StagedPacket) :
    StagedEqv
      (stagedAdd (stagedKeepVacuum A) (stagedRemoveVacuum A)) A := by
  intro s
  refine Q'.eqv_trans _
    (coeffAt (stagedKeepVacuum A).packet s +
      coeffAt (stagedRemoveVacuum A).packet s) _
    (coeffAt_stagedAdd (stagedKeepVacuum A)
      (stagedRemoveVacuum A) s) ?_
  by_cases hs : s = 0
  · refine Q'.eqv_trans _
      (coeffAt A.packet s + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (by simpa [hs] using coeffAt_stagedKeepVacuum A s)
        (by simpa [hs] using coeffAt_stagedRemoveVacuum A s)
    · exact q_add_zero_eqv _
  · refine Q'.eqv_trans _
      (0 + coeffAt A.packet s) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (by simpa [hs] using coeffAt_stagedKeepVacuum A s)
        (by simpa [hs] using coeffAt_stagedRemoveVacuum A s)
    · exact q_zero_add_eqv _

private theorem keep_remove_term_zero (A : StagedPacket) (s : Nat) :
    packetEigen s *
        (coeffAt (stagedKeepVacuum A).packet s *
          coeffAt (stagedRemoveVacuum A).packet s) ≈ 0 := by
  by_cases hs : s = 0
  · refine Q'.eqv_trans _
      (packetEigen s *
        (coeffAt (stagedKeepVacuum A).packet s * 0)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by
          simpa [hs] using coeffAt_stagedRemoveVacuum A s))
    · exact Q'.eqv_trans _ (packetEigen s * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        (Q'.mul_zero_eqv _)
  · refine Q'.eqv_trans _
      (packetEigen s *
        (0 * coeffAt (stagedRemoveVacuum A).packet s)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by
          simpa [hs] using coeffAt_stagedKeepVacuum A s))
    · exact Q'.eqv_trans _ (packetEigen s * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
        (Q'.mul_zero_eqv _)

/-- The complementary carrier pieces are exactly orthogonal in the physical
interacting Wilson Gram. -/
theorem stagedKeep_remove_orthogonal (A : StagedPacket) :
    stagedGram (stagedKeepVacuum A) (stagedRemoveVacuum A) ≈ 0 := by
  unfold stagedGram
  refine Q'.eqv_trans _
    (fsum (fun s => packetEigen s *
      (coeffAt
          (padPacket
            (Nat.le_max_left (stagedKeepVacuum A).cutoff
              (stagedRemoveVacuum A).cutoff)
            (stagedKeepVacuum A).packet) s *
        coeffAt
          (padPacket
            (Nat.le_max_right (stagedKeepVacuum A).cutoff
              (stagedRemoveVacuum A).cutoff)
            (stagedRemoveVacuum A).packet) s))
      (Nat.max (stagedKeepVacuum A).cutoff
        (stagedRemoveVacuum A).cutoff + 1)) _
    (packetWilsonGram_diagonal _ _) ?_
  apply fsum_eqv_zero
  intro s
  rw [coeffAt_padPacket, coeffAt_padPacket]
  exact keep_remove_term_zero A s

/-! ## Contractivity in the exact Wilson Gram -/

private theorem remove_term_le (A : StagedPacket) (s : Nat) :
    packetEigen s *
        (coeffAt (stagedRemoveVacuum A).packet s *
          coeffAt (stagedRemoveVacuum A).packet s) ≤
      packetEigen s * (coeffAt A.packet s * coeffAt A.packet s) := by
  by_cases hs : s = 0
  · have hz := coeffAt_stagedRemoveVacuum A s
    rw [if_pos hs] at hz
    have hl : packetEigen s *
        (coeffAt (stagedRemoveVacuum A).packet s *
          coeffAt (stagedRemoveVacuum A).packet s) ≈ 0 := by
      refine Q'.eqv_trans _ (packetEigen s * (0 * 0)) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _
            (0 * coeffAt (stagedRemoveVacuum A).packet s) _
            (Q'.mul_eqv_congr_right _ _ _ hz)
            (Q'.zero_mul_eqv _))) ?_
      exact Q'.eqv_trans _ (packetEigen s * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0))
        (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hl)
      (Q'.mul_nonneg _ _ (packetEigen_nonneg s)
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
          (coeffAt A.packet s)))
  · have he := coeffAt_stagedRemoveVacuum A s
    rw [if_neg hs] at he
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _
          (coeffAt A.packet s *
            coeffAt (stagedRemoveVacuum A).packet s) _
          (Q'.mul_eqv_congr_right _ _ _ he)
          (Q'.mul_eqv_congr_left _ _ _ he)))

theorem stagedRemoveVacuum_contraction (A : StagedPacket) :
    stagedGram (stagedRemoveVacuum A) (stagedRemoveVacuum A) ≤
      stagedGram A A := by
  have hsum := fsum_le_fsum (remove_term_le A) (A.cutoff + 1)
  refine le_of_eqv_le (stagedGram_self_eq_packet (stagedRemoveVacuum A)) ?_
  refine le_of_eqv_le
    (packetWilsonGram_diagonal
      (stagedRemoveVacuum A).packet (stagedRemoveVacuum A).packet) ?_
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm (packetWilsonGram_diagonal A.packet A.packet)))
      (Q'.le_of_eqv (Q'.eqv_symm (stagedGram_self_eq_packet A))))

theorem stagedRemoveVacuum_distSq_contraction (A B : StagedPacket) :
    packetColimitGNS.distSqQ
        (stagedRemoveVacuum A) (stagedRemoveVacuum B) ≤
      packetColimitGNS.distSqQ A B := by
  have hsub := stagedRemoveVacuum_sub A B
  exact le_of_eqv_le
    (Q'.eqv_symm (packetColimitGNS.B_diag_congr hsub))
    (stagedRemoveVacuum_contraction (packetColimitGNS.sub A B))

/-- The excited projection as a contractive rational-linear symbol. -/
def removeVacuumSymbol : DiagonalTransferSymbol packetColimitSmulGNS where
  Dv := stagedRemoveVacuum
  Dv_congr := stagedRemoveVacuum_congr
  distSqQ_Dv := stagedRemoveVacuum_distSq_contraction
  Dv_add := stagedRemoveVacuum_add
  Dv_smul := stagedRemoveVacuum_smul

/-! ## The completed excited projection -/

def completedRemoveVacuum :
    GNSCompletionSpace packetColimitGNS →
      GNSCompletionSpace packetColimitGNS :=
  removeVacuumSymbol.TqSymb

theorem completedRemoveVacuum_embed (A : StagedPacket) :
    completedRemoveVacuum (embedV packetColimitGNS A) =
      embedV packetColimitGNS (stagedRemoveVacuum A) :=
  removeVacuumSymbol.TqSymb_embed A

theorem completedRemoveVacuum_idempotent
    (x : GNSCompletionSpace packetColimitGNS) :
    completedRemoveVacuum (completedRemoveVacuum x) =
      completedRemoveVacuum x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun n _ => le_of_eqv_le
    (rad_of_veq packetColimitGNS
      (stagedRemoveVacuum_idempotent (u.seq n)))
    (Q'.le_of_lt hepsilon)⟩

theorem completedRemoveVacuum_transfer_commute
    (x : GNSCompletionSpace packetColimitGNS) :
    completedPacketTransfer (completedRemoveVacuum x) =
      completedRemoveVacuum (completedPacketTransfer x) := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun n _ => le_of_eqv_le
    (rad_of_veq packetColimitGNS
      (stagedRemoveVacuum_transfer_commute (u.seq n)))
    (Q'.le_of_lt hepsilon)⟩

theorem stagedRemoveVacuum_vacuum :
    StagedEqv (stagedRemoveVacuum stagedVacuum) stagedZero := by
  intro s
  by_cases hs : s = 0
  · refine Q'.eqv_trans _ 0 _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum stagedVacuum s) ?_
    exact Q'.eqv_symm (coeffAt_stagedZero s)
  · have hv : coeffAt stagedVacuum.packet s = 0 := by
      change coeffAt (vacuumPacket 0) s = 0
      exact coeffAt_of_gt (vacuumPacket 0) (by omega)
    refine Q'.eqv_trans _ (coeffAt stagedVacuum.packet s) _ (by
      simpa [hs] using coeffAt_stagedRemoveVacuum stagedVacuum s) ?_
    rw [hv]
    exact Q'.eqv_symm (coeffAt_stagedZero s)

theorem completedRemoveVacuum_vacuum :
    completedRemoveVacuum completedPacketVacuum =
      embedV packetColimitGNS packetColimitGNS.zero := by
  refine Eq.trans (completedRemoveVacuum_embed stagedVacuum) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS stagedRemoveVacuum_vacuum)

/-- The completed complementary vacuum part.  Its representatives retain only
the trivial-character coordinate. -/
def completedKeepVacuum (x : GNSCompletionSpace packetColimitGNS) :
    GNSCompletionSpace packetColimitGNS :=
  packetColimitGNS.cSub x (completedRemoveVacuum x)

theorem completedKeepVacuum_fixed
    (x : GNSCompletionSpace packetColimitGNS) :
    completedPacketTransfer (completedKeepVacuum x) =
      completedKeepVacuum x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun n _ => le_of_eqv_le
    (rad_of_veq packetColimitGNS
      (stagedKeepVacuum_fixed (u.seq n)))
    (Q'.le_of_lt hepsilon)⟩

/-- Canonical completed decomposition into a transfer-fixed vacuum part and the
excited projection. -/
theorem completedKeep_add_remove
    (x : GNSCompletionSpace packetColimitGNS) :
    packetColimitGNS.cAdd (completedKeepVacuum x)
      (completedRemoveVacuum x) = x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun n _ => le_of_eqv_le
    (rad_of_veq packetColimitGNS
      (stagedKeep_add_remove (u.seq n)))
    (Q'.le_of_lt hepsilon)⟩

/-- The completed vacuum/excited decomposition is orthogonal, obtained by
passing the exact carrier identity through the explicit Cauchy limit. -/
theorem completedKeep_remove_orthogonal
    (x : GNSCompletionSpace packetColimitGNS) :
    packetColimitGNS.cinnerCompl (completedKeepVacuum x)
      (completedRemoveVacuum x) = CReal.RCzero := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun N => CReal.ofQ'
      (packetColimitGNS.cInnerSeq
        (packetColimitGNS.cAddCauchy u
          (packetColimitGNS.cNegCauchy
            (removeVacuumSymbol.cDiagCauchy u)))
        (removeVacuumSymbol.cDiagCauchy u) N))
    (bSeq := fun N => CReal.ofQ' (CReal.czero.approx N))
    ?_ (CReal.convergesTo_ofQ'CauchySeq _ _)
      (CReal.convergesTo_self CReal.czero)
  intro N
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact stagedKeep_remove_orthogonal (u.seq N)

/-- Every completed vector has a canonically produced excited representative,
so the exact `1/8` edge no longer depends on a caller-supplied vacuum-free
presentation. -/
theorem completedPacketTransfer_projected_edge
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer (completedRemoveVacuum x))
        (completedPacketTransfer (completedRemoveVacuum x)))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedRemoveVacuum x))
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedRemoveVacuum x))) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact cinnerRep_vacuumFree_edge_contraction
    (removeVacuumSymbol.cDiagCauchy u)
    (fun n => stagedRemoveVacuum_vacuumFree (u.seq n))

end YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.coeffAt_stagedRemoveVacuum
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedRemoveVacuum_congr
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedRemoveVacuum_idempotent
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedRemoveVacuum_transfer_commute
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedKeepVacuum_fixed
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedKeep_add_remove
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedKeep_remove_orthogonal
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.stagedRemoveVacuum_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.removeVacuumSymbol
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedRemoveVacuum
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedRemoveVacuum_idempotent
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedRemoveVacuum_transfer_commute
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedRemoveVacuum_vacuum
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedKeepVacuum_fixed
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedKeep_add_remove
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedKeep_remove_orthogonal
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection.completedPacketTransfer_projected_edge
