/-
# Completed GNS realization of the globally projected arbitrary bigon

The common-label gauge quotient and global vacuum projection of an arbitrary
packet bigon are finite character packets.  This module embeds that packet in
the all-character GNS completion and proves that the physical two-link cycle
evolution is literally two applications of the already constructed completed
transfer operator.

The completed state is independent of both input cutoffs, lies in the canonical
excited projection, and its first and second transfer iterates remain in that
range.  The second iterate is identified coefficientwise with the exact cycle
transfer used by the located finite spectral model.

Honest scope: this completes the operator/model linkage for the bivalent bigon
only.  General vertex-intertwiner quotients and finite-volume assembly remain.
-/

import YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap
import YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap

namespace YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection
open YMGap.Continuum.SU2FiniteCharacterPacketColimitProjectedSpectralGap
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge
open YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility
open YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient

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

def arbitraryBigonProjectedPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    CharacterPacket (2 * sharedCutoff N M) where
  coeff i := arbitraryBigonGlobalExcited P Q i.val

theorem coeffAt_arbitraryBigonProjectedPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    coeffAt (arbitraryBigonProjectedPacket P Q) s ≈
      arbitraryBigonGlobalExcited P Q s := by
  by_cases hs : s < 2 * sharedCutoff N M + 1
  · rw [coeffAt_of_lt _ hs]
    exact Q'.eqv_refl _
  · have hgt : 2 * sharedCutoff N M < s := by omega
    rw [coeffAt_of_gt _ hgt]
    have hs0 : s ≠ 0 := by omega
    cases s with
    | zero => exact False.elim (hs0 rfl)
    | succ t =>
        refine Q'.eqv_symm (Q'.eqv_trans _
          (coeffAt (arbitraryBigonPacket P Q).1 (t + 1) *
            coeffAt (arbitraryBigonPacket P Q).2 (t + 1)) _ ?_ ?_)
        · exact arbitraryBigonGaugePacket_exact P Q (t + 1)
        · have hgt' : 2 * sharedCutoff N M < t + 1 := by omega
          rw [coeffAt_of_gt _ hgt', coeffAt_of_gt _ hgt']
          exact Q'.zero_mul_eqv 0

theorem arbitraryBigonProjectedPacket_vacuumFree {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    coeffAt (arbitraryBigonProjectedPacket P Q) 0 ≈ 0 :=
  Q'.eqv_trans _ _ _ (coeffAt_arbitraryBigonProjectedPacket P Q 0)
    (arbitraryBigonGlobalExcited_zero P Q)

private theorem sharedCutoff_mono_here {N N' M M' : Nat}
    (hNN : N ≤ N') (hMM : M ≤ M') :
    sharedCutoff N M ≤ sharedCutoff N' M' := by
  apply (Nat.max_le).2
  exact ⟨Nat.le_trans hNN (Nat.le_max_left _ _),
    Nat.le_trans hMM (Nat.le_max_right _ _)⟩

/-- The projected packet is coherent under unrelated enlargement of the two
input cutoffs. -/
theorem arbitraryBigonProjectedPacket_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PacketEqv
      (arbitraryBigonProjectedPacket (padPacket hNN P) (padPacket hMM Q))
      (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono_here hNN hMM))
        (arbitraryBigonProjectedPacket P Q)) := by
  intro i
  change arbitraryBigonGlobalExcited
      (padPacket hNN P) (padPacket hMM Q) i.val ≈
    coeffAt (arbitraryBigonProjectedPacket P Q) i.val
  exact Q'.eqv_trans _ _ _
    (arbitraryBigonGlobalExcited_pad_independent hNN hMM P Q i.val)
    (Q'.eqv_symm (coeffAt_arbitraryBigonProjectedPacket P Q i.val))

def arbitraryBigonProjectedStage {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : StagedPacket :=
  stagePacket (arbitraryBigonProjectedPacket P Q)

def completedArbitraryBigonProjectedState {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    GNSCompletionSpace packetColimitGNS :=
  embedV packetColimitGNS (arbitraryBigonProjectedStage P Q)

/-- Independent cutoff enlargement becomes literal equality in the completed
GNS carrier. -/
theorem completedArbitraryBigonProjectedState_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedArbitraryBigonProjectedState
        (padPacket hNN P) (padPacket hMM Q) =
      completedArbitraryBigonProjectedState P Q := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s =>
      Q'.eqv_trans _ _ _
        (coeffAt_arbitraryBigonProjectedPacket
          (padPacket hNN P) (padPacket hMM Q) s)
        (Q'.eqv_trans _ _ _
          (arbitraryBigonGlobalExcited_pad_independent hNN hMM P Q s)
          (Q'.eqv_symm
            (coeffAt_arbitraryBigonProjectedPacket P Q s)))))

private theorem stagedRemove_projected_eq {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    StagedEqv
      (stagedRemoveVacuum (arbitraryBigonProjectedStage P Q))
      (arbitraryBigonProjectedStage P Q) := by
  intro s
  by_cases hs : s = 0
  · subst s
    refine Q'.eqv_trans _ 0 _ (by
      simpa using coeffAt_stagedRemoveVacuum
        (arbitraryBigonProjectedStage P Q) 0) ?_
    exact Q'.eqv_symm (arbitraryBigonProjectedPacket_vacuumFree P Q)
  · simpa [hs] using coeffAt_stagedRemoveVacuum
      (arbitraryBigonProjectedStage P Q) s

/-- The completed global-bigon state already lies in the canonical excited
range; applying the projector changes nothing. -/
theorem completedRemoveVacuum_arbitraryBigonProjectedState {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedRemoveVacuum (completedArbitraryBigonProjectedState P Q) =
      completedArbitraryBigonProjectedState P Q := by
  refine Eq.trans
    (completedRemoveVacuum_embed (arbitraryBigonProjectedStage P Q)) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (stagedRemove_projected_eq P Q))

/-- The first physical transfer iterate remains globally excited. -/
theorem completedRemoveVacuum_firstTransfer {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedRemoveVacuum
        (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)) =
      completedPacketTransfer (completedArbitraryBigonProjectedState P Q) := by
  rw [← completedRemoveVacuum_transfer_commute,
    completedRemoveVacuum_arbitraryBigonProjectedState]

/-- Two-link evolution is two literal applications of the actual completed
packet transfer. -/
theorem completedArbitraryBigon_twoLinkTransfer {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedPacketTransfer
        (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)) =
      embedV packetColimitGNS
        (stagePacket
          (packetTransfer (packetTransfer
            (arbitraryBigonProjectedPacket P Q)))) := by
  unfold completedArbitraryBigonProjectedState
  rw [completedPacketTransfer_embed, completedPacketTransfer_embed]
  rfl

def arbitraryBigonCycleTransferredPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    CharacterPacket (2 * sharedCutoff N M) where
  coeff i := cycleTransfer arbitraryBigonOrder
    (arbitraryBigonGlobalExcited P Q) i.val

/-- The double completed-transfer packet is coefficientwise the exact
two-link cycle transfer from the globally projected spectral model. -/
theorem doublePacketTransfer_eq_cycle {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    PacketEqv
      (packetTransfer (packetTransfer (arbitraryBigonProjectedPacket P Q)))
      (arbitraryBigonCycleTransferredPacket P Q) := by
  intro i
  change packetEigen i.val *
      (packetEigen i.val * arbitraryBigonGlobalExcited P Q i.val) ≈
    cycleTransfer arbitraryBigonOrder
      (arbitraryBigonGlobalExcited P Q) i.val
  unfold cycleTransfer cycleEigen arbitraryBigonOrder eliminateLinks
  change packetEigen i.val * (packetEigen i.val *
      arbitraryBigonGlobalExcited P Q i.val) ≈
    (packetEigen i.val * (packetEigen i.val * 1)) *
      arbitraryBigonGlobalExcited P Q i.val
  ring_qeqv

/-- Completed operator/model linkage for the bivalent bigon. -/
theorem completedArbitraryBigon_twoLinkTransfer_eq_cycle {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    completedPacketTransfer
        (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)) =
      embedV packetColimitGNS
        (stagePacket (arbitraryBigonCycleTransferredPacket P Q)) := by
  refine Eq.trans (completedArbitraryBigon_twoLinkTransfer P Q) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s =>
      coeffAt_packetEqv (doublePacketTransfer_eq_cycle P Q) s))

/-- The exact completed `1/8` norm edge applies to the second link step without
any representative-side hypothesis. -/
theorem completedArbitraryBigon_secondLink_edge {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer
          (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)))
        (completedPacketTransfer
          (completedPacketTransfer (completedArbitraryBigonProjectedState P Q))))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)))
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedPacketTransfer (completedArbitraryBigonProjectedState P Q)))) := by
  simpa [completedRemoveVacuum_firstTransfer P Q] using
    completedPacketTransfer_projected_edge
      (completedPacketTransfer (completedArbitraryBigonProjectedState P Q))

end YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap

#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.coeffAt_arbitraryBigonProjectedPacket
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.arbitraryBigonProjectedPacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.completedArbitraryBigonProjectedState_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.completedRemoveVacuum_arbitraryBigonProjectedState
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.completedArbitraryBigon_twoLinkTransfer
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.doublePacketTransfer_eq_cycle
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.completedArbitraryBigon_twoLinkTransfer_eq_cycle
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonCompletedGlobalGap.completedArbitraryBigon_secondLink_edge
