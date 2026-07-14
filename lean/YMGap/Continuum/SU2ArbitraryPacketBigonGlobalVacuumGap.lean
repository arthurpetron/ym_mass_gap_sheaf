/-
# Global vacuum projection and located gap for arbitrary packet bigons

The arbitrary-packet bigon retains its two oppositely oriented fused links.
The bivalent gauge quotient must next impose one common irrep label around the
cycle; multiplying the forward and reverse coefficients at that label performs
this quotient exactly.  Only after that simultaneous quotient is it correct to
remove the unique global vacuum label.

This file connects the arbitrary-cutoff bigon construction to the existing
global-cycle transfer and spectral localization.  It proves independent-cutoff
coherence after gauge collapse, exact intertwining with simultaneous link
transfer, the uniform `1/64` squared-norm edge, and a concrete located spectral
model with gap margin `63/64`.

Honest scope: this is the globally projected bivalent two-link cycle.  It does
not supply trivalent intertwiners or a general finite-lattice Hilbert space.
-/

import YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility
import YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization

namespace YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2ArbitraryPacketSharedLinkFusionBridge
open YMGap.Continuum.SU2ArbitraryPacketBigonCycleCompatibility
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient
open YMGap.Continuum.SU2GlobalVacuumCycleSpectralLocalization

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sharedCutoff_mono_here {N N' M M' : Nat}
    (hNN : N ≤ N') (hMM : M ≤ M') :
    sharedCutoff N M ≤ sharedCutoff N' M' := by
  apply (Nat.max_le).2
  exact ⟨Nat.le_trans hNN (Nat.le_max_left _ _),
    Nat.le_trans hMM (Nat.le_max_right _ _)⟩

/-! ## The simultaneous common-label quotient -/

/-- The two oriented arbitrary-packet links as a link-indexed coefficient
table.  Only links `0` and `1` occur in `arbitraryBigonOrder`. -/
def arbitraryBigonLinkPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : LinkPacket :=
  fun l s => if l = 0 then coeffAt (arbitraryBigonPacket P Q).1 s
    else coeffAt (arbitraryBigonPacket P Q).2 s

def arbitraryBigonOrder : List Nat := [0, 1]

/-- Gauge-compatible coefficient: both oriented links carry the same label. -/
def arbitraryBigonGaugePacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : Nat → Q' :=
  cycleGaugeCollapse (arbitraryBigonLinkPacket P Q) arbitraryBigonOrder

/-- The common-label quotient is exactly the forward/reverse coefficient
product, rather than the independent-link tensor product. -/
theorem arbitraryBigonGaugePacket_exact {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    arbitraryBigonGaugePacket P Q s ≈
      coeffAt (arbitraryBigonPacket P Q).1 s *
        coeffAt (arbitraryBigonPacket P Q).2 s := by
  unfold arbitraryBigonGaugePacket cycleGaugeCollapse arbitraryBigonOrder
    arbitraryBigonLinkPacket eliminateLinks
  simp only [if_pos]
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)

/-- Orientation closure turns the gauge-compatible coefficient into the
square of the forward fused coefficient. -/
theorem arbitraryBigonGaugePacket_eq_forward_square {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    arbitraryBigonGaugePacket P Q s ≈
      coeffAt (arbitraryBigonPacket P Q).1 s *
        coeffAt (arbitraryBigonPacket P Q).1 s :=
  Q'.eqv_trans _ _ _ (arbitraryBigonGaugePacket_exact P Q s)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (coeffAt_packetEqv (arbitraryBigon_orientation_closure P Q) s)))

private theorem paddedBigonCoeff {N N' M M' : Nat}
    (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) (side s : Nat) :
    (if side = 0 then
        coeffAt (arbitraryBigonPacket (padPacket hNN P) (padPacket hMM Q)).1 s
      else
        coeffAt (arbitraryBigonPacket (padPacket hNN P) (padPacket hMM Q)).2 s) ≈
    (if side = 0 then coeffAt (arbitraryBigonPacket P Q).1 s
      else coeffAt (arbitraryBigonPacket P Q).2 s) := by
  have hbig := arbitraryBigonPacket_pad_independent hNN hMM P Q
  by_cases hs : side = 0
  · rw [if_pos hs, if_pos hs]
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono_here hNN hMM))
          (arbitraryBigonPacket P Q).1) s) _
      (coeffAt_packetEqv hbig.1 s) ?_
    rw [coeffAt_padPacket]
    exact Q'.eqv_refl _
  · rw [if_neg hs, if_neg hs]
    refine Q'.eqv_trans _
      (coeffAt
        (padPacket (Nat.mul_le_mul_left 2 (sharedCutoff_mono_here hNN hMM))
          (arbitraryBigonPacket P Q).2) s) _
      (coeffAt_packetEqv hbig.2 s) ?_
    rw [coeffAt_padPacket]
    exact Q'.eqv_refl _

/-- Independent enlargement of both plaquette cutoffs leaves the common-label
cycle quotient unchanged coefficientwise. -/
theorem arbitraryBigonGaugePacket_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    arbitraryBigonGaugePacket (padPacket hNN P) (padPacket hMM Q) s ≈
      arbitraryBigonGaugePacket P Q s := by
  refine Q'.eqv_trans _
    (coeffAt
        (arbitraryBigonPacket (padPacket hNN P) (padPacket hMM Q)).1 s *
      coeffAt
        (arbitraryBigonPacket (padPacket hNN P) (padPacket hMM Q)).2 s) _
    (arbitraryBigonGaugePacket_exact _ _ s) ?_
  refine Q'.eqv_trans _
    (coeffAt (arbitraryBigonPacket P Q).1 s *
      coeffAt (arbitraryBigonPacket P Q).2 s) _ ?_ ?_
  · exact q_mul_congr
      (paddedBigonCoeff hNN hMM P Q 0 s)
      (paddedBigonCoeff hNN hMM P Q 1 s)
  · exact Q'.eqv_symm (arbitraryBigonGaugePacket_exact P Q s)

/-! ## Global vacuum projection and cutoff coherence -/

def arbitraryBigonGlobalExcited {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : Nat → Q' :=
  globalVacuumProject (arbitraryBigonGaugePacket P Q)

theorem arbitraryBigonGlobalExcited_zero {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    arbitraryBigonGlobalExcited P Q 0 ≈ 0 :=
  globalVacuumProject_zero _

theorem arbitraryBigonGlobalExcited_pad_independent
    {N N' M M' : Nat} (hNN : N ≤ N') (hMM : M ≤ M')
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    arbitraryBigonGlobalExcited (padPacket hNN P) (padPacket hMM Q) s ≈
      arbitraryBigonGlobalExcited P Q s := by
  cases s with
  | zero => exact Q'.eqv_refl 0
  | succ s => exact arbitraryBigonGaugePacket_pad_independent hNN hMM P Q (s + 1)

/-! ## Simultaneous physical transfer descends to the quotient -/

/-- Both actual packet transfers, retained as one link table. -/
def arbitraryBigonTransferredLinkPacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : LinkPacket :=
  fun l s => if l = 0 then
      coeffAt (packetTransfer (arbitraryBigonPacket P Q).1) s
    else coeffAt (packetTransfer (arbitraryBigonPacket P Q).2) s

theorem arbitraryBigonTransferredLinkPacket_eq {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (l s : Nat) :
    arbitraryBigonTransferredLinkPacket P Q l s ≈
      transferredLinkPacket (arbitraryBigonLinkPacket P Q) l s := by
  by_cases hl : l = 0
  · unfold arbitraryBigonTransferredLinkPacket transferredLinkPacket
      arbitraryBigonLinkPacket
    rw [if_pos hl, if_pos hl]
    exact coeffAt_packetTransfer _ s
  · unfold arbitraryBigonTransferredLinkPacket transferredLinkPacket
      arbitraryBigonLinkPacket
    rw [if_neg hl, if_neg hl]
    exact coeffAt_packetTransfer _ s

private theorem eliminateLinks_congr {f g : Nat → Q'}
    (h : ∀ l, f l ≈ g l) : ∀ order,
    eliminateLinks f order ≈ eliminateLinks g order
  | [] => Q'.eqv_refl 1
  | l :: rest => q_mul_congr (h l) (eliminateLinks_congr h rest)

def arbitraryBigonTransferredGaugePacket {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : Nat → Q' :=
  cycleGaugeCollapse (arbitraryBigonTransferredLinkPacket P Q)
    arbitraryBigonOrder

/-- Applying the physical packet transfer on both oriented links before the
gauge quotient equals the exact two-link cycle transfer after collapse. -/
theorem arbitraryBigonGaugePacket_transfer_intertwiner {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    arbitraryBigonTransferredGaugePacket P Q s ≈
      cycleTransfer arbitraryBigonOrder (arbitraryBigonGaugePacket P Q) s := by
  refine Q'.eqv_trans _
    (cycleGaugeCollapse
      (transferredLinkPacket (arbitraryBigonLinkPacket P Q))
      arbitraryBigonOrder s) _ ?_ ?_
  · unfold arbitraryBigonTransferredGaugePacket cycleGaugeCollapse
    exact eliminateLinks_congr
      (fun l => arbitraryBigonTransferredLinkPacket_eq P Q l s)
      arbitraryBigonOrder
  · exact cycleGaugeCollapse_transfer_intertwiner
      (arbitraryBigonLinkPacket P Q) arbitraryBigonOrder s

private theorem globalVacuumProject_congr {f g : Nat → Q'}
    (h : ∀ s, f s ≈ g s) (s : Nat) :
    globalVacuumProject f s ≈ globalVacuumProject g s := by
  cases s with
  | zero => exact Q'.eqv_refl 0
  | succ s => exact h (s + 1)

/-- Global vacuum projection commutes with the simultaneous physical bigon
transfer, after identifying linkwise transfer with cycle transfer. -/
theorem arbitraryBigonGlobalExcited_transfer_commutes {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) (s : Nat) :
    cycleTransfer arbitraryBigonOrder (arbitraryBigonGlobalExcited P Q) s ≈
      globalVacuumProject (arbitraryBigonTransferredGaugePacket P Q) s := by
  refine Q'.eqv_trans _
    (globalVacuumProject
      (cycleTransfer arbitraryBigonOrder (arbitraryBigonGaugePacket P Q)) s) _
    (globalVacuumProject_transfer_commutes arbitraryBigonOrder
      (arbitraryBigonGaugePacket P Q) s) ?_
  exact globalVacuumProject_congr
    (fun t => Q'.eqv_symm
      (arbitraryBigonGaugePacket_transfer_intertwiner P Q t)) s

/-! ## Uniform cycle gap and its linked finite spectral model -/

def arbitraryBigonModeCount (N M : Nat) : Nat :=
  2 * sharedCutoff N M + 1

/-- Every arbitrary-packet bigon, after the correct global projection,
contracts by the same two-link squared edge `1/64`. -/
theorem arbitraryBigon_global_uniform_contraction {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    modeNorm
        (cycleTransfer arbitraryBigonOrder (arbitraryBigonGlobalExcited P Q))
        (arbitraryBigonModeCount N M) ≤
      (eighth * eighth) *
        modeNorm (arbitraryBigonGlobalExcited P Q)
          (arbitraryBigonModeCount N M) :=
  finite_cycle_global_vacuum_contraction
    (arbitraryBigonGaugePacket P Q) 0 [1] (arbitraryBigonModeCount N M)

def arbitraryBigonProjectedSpectralModel {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) : SpectralModel :=
  projectedCycleSpectralModel (arbitraryBigonGaugePacket P Q)
    0 [1] (arbitraryBigonModeCount N M)

def arbitraryBigonProjectedLocatedGap {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    LocatedSpectralGap (arbitraryBigonProjectedSpectralModel P Q) :=
  projectedCycleLocatedGap (arbitraryBigonGaugePacket P Q)
    0 [1] (arbitraryBigonModeCount N M)

theorem arbitraryBigonProjected_gapMargin_exact {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    (arbitraryBigonProjectedLocatedGap P Q).gapMargin ≈
      Q'.mkPos 63 64 (by decide) :=
  projectedCycle_gapMargin_exact (arbitraryBigonGaugePacket P Q)
    0 [1] (arbitraryBigonModeCount N M)

/-- Time zero of the linked model is the exact globally projected bigon norm. -/
theorem arbitraryBigonProjected_corr_zero {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    corr (arbitraryBigonProjectedSpectralModel P Q) 0 ≈
      modeNorm (arbitraryBigonGlobalExcited P Q)
        (arbitraryBigonModeCount N M) :=
  projectedCycle_corr_zero_eq_norm (arbitraryBigonGaugePacket P Q)
    0 [1] (arbitraryBigonModeCount N M)

/-- Time one is the exact norm after simultaneous transfer around both links. -/
theorem arbitraryBigonProjected_corr_one {N M : Nat}
    (P : CharacterPacket N) (Q : CharacterPacket M) :
    corr (arbitraryBigonProjectedSpectralModel P Q) 1 ≈
      modeNorm
        (cycleTransfer arbitraryBigonOrder (arbitraryBigonGlobalExcited P Q))
        (arbitraryBigonModeCount N M) :=
  projectedCycle_corr_one_eq_transferred_norm
    (arbitraryBigonGaugePacket P Q) 0 [1] (arbitraryBigonModeCount N M)

end YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap

#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonGaugePacket_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonGaugePacket_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonGlobalExcited_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonGaugePacket_transfer_intertwiner
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonGlobalExcited_transfer_commutes
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigon_global_uniform_contraction
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonProjectedLocatedGap
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonProjected_gapMargin_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketBigonGlobalVacuumGap.arbitraryBigonProjected_corr_one
