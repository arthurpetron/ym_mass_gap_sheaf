/-
# Arbitrary finite cycles in the completed character-packet GNS space

The global common-label cycle quotient acts by one exact Wilson eigenvalue
for every eliminated link.  This module identifies that finite cycle action
with literal iteration of the already constructed completed transfer
operator.  The result is uniform in the finite cutoff and independent of the
names attached to the links.

The excited projection commutes with every finite iterate.  Consequently each
nonempty projected cycle has the sharp `1/8` edge on its outermost transfer
step, while all preceding steps remain in the same completed excited range.

Honest scope: this treats the common-label bivalent cycle sector.  General
multi-vertex spin networks additionally require compatible intertwiner
contractions at their vertices.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection
import YMGap.Continuum.SU2GlobalVacuumCycleQuotient

namespace YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteCharacterPacketColimit
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection
open YMGap.Continuum.SU2GlobalVacuumCycleQuotient

local infix:50 " ≈ " => Q'.eqv

/-- Iterate the physical packet transfer once for every link of a finite
cycle.  Link names do not enter the common-label sector. -/
def packetCycleTransfer {N : Nat} :
    List Nat → CharacterPacket N → CharacterPacket N
  | [], P => P
  | _ :: rest, P => packetTransfer (packetCycleTransfer rest P)

/-- Coefficientwise, finite packet iteration is exactly the global cycle
transfer by the product of the link eigenvalues. -/
theorem coeffAt_packetCycleTransfer {N : Nat} (order : List Nat)
    (P : CharacterPacket N) (s : Nat) :
    coeffAt (packetCycleTransfer order P) s ≈
      cycleTransfer order (fun t => coeffAt P t) s := by
  induction order with
  | nil =>
      unfold packetCycleTransfer cycleTransfer cycleEigen eliminateLinks
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | cons l rest ih =>
      change coeffAt (packetTransfer (packetCycleTransfer rest P)) s ≈ _
      refine Q'.eqv_trans _
        (packetEigen s * coeffAt (packetCycleTransfer rest P) s) _
        (coeffAt_packetTransfer (packetCycleTransfer rest P) s) ?_
      refine Q'.eqv_trans _
        (packetEigen s *
          cycleTransfer rest (fun t => coeffAt P t) s) _
        (Q'.mul_eqv_congr_left _ _ _ ih) ?_
      change packetEigen s * (cycleEigen rest s * coeffAt P s) ≈
        (packetEigen s * cycleEigen rest s) * coeffAt P s
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- The finite packet whose coefficients are the exact common-label cycle
transfer of an input packet. -/
def cycleTransferredPacket {N : Nat} (order : List Nat)
    (P : CharacterPacket N) : CharacterPacket N where
  coeff i := cycleTransfer order (fun s => coeffAt P s) i.val

theorem packetCycleTransfer_eq_cycleTransferredPacket {N : Nat}
    (order : List Nat) (P : CharacterPacket N) :
    PacketEqv (packetCycleTransfer order P)
      (cycleTransferredPacket order P) := by
  intro i
  have h := coeffAt_packetCycleTransfer order P i.val
  rw [coeffAt_of_lt (packetCycleTransfer order P) i.isLt] at h
  exact h

/-- Vacuum freedom is preserved by every finite cycle iterate. -/
theorem packetCycleTransfer_vacuumFree {N : Nat} (order : List Nat)
    (P : CharacterPacket N) (hP : coeffAt P 0 ≈ 0) :
    coeffAt (packetCycleTransfer order P) 0 ≈ 0 := by
  refine Q'.eqv_trans _
    (cycleTransfer order (fun s => coeffAt P s) 0) _
    (coeffAt_packetCycleTransfer order P 0) ?_
  unfold cycleTransfer
  refine Q'.eqv_trans _ (cycleEigen order 0 * 0) _
    (Q'.mul_eqv_congr_left _ _ _ hP) ?_
  exact Q'.mul_zero_eqv _

/-- Literal finite iteration of the physical transfer on the completed GNS
space. -/
def completedPacketCycleTransfer : List Nat →
    GNSCompletionSpace packetColimitGNS →
      GNSCompletionSpace packetColimitGNS
  | [], x => x
  | _ :: rest, x =>
      completedPacketTransfer (completedPacketCycleTransfer rest x)

/-- Finite iteration commutes exactly with the dense finite-packet embedding. -/
theorem completedPacketCycleTransfer_embed {N : Nat} (order : List Nat)
    (P : CharacterPacket N) :
    completedPacketCycleTransfer order
        (embedV packetColimitGNS (stagePacket P)) =
      embedV packetColimitGNS
        (stagePacket (packetCycleTransfer order P)) := by
  induction order with
  | nil => rfl
  | cons l rest ih =>
      unfold completedPacketCycleTransfer packetCycleTransfer
      rw [ih, completedPacketTransfer_embed]
      rfl

/-- The completed iterate is the embedded exact common-label cycle packet,
not merely an isospectral finite model. -/
theorem completedPacketCycleTransfer_eq_cycleTransferredPacket {N : Nat}
    (order : List Nat) (P : CharacterPacket N) :
    completedPacketCycleTransfer order
        (embedV packetColimitGNS (stagePacket P)) =
      embedV packetColimitGNS
        (stagePacket (cycleTransferredPacket order P)) := by
  refine Eq.trans (completedPacketCycleTransfer_embed order P) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s =>
      coeffAt_packetEqv
        (packetCycleTransfer_eq_cycleTransferredPacket order P) s))

/-- The canonical completed excited projection commutes with an arbitrary
finite cycle iterate. -/
theorem completedRemoveVacuum_cycle_commute (order : List Nat)
    (x : GNSCompletionSpace packetColimitGNS) :
    completedRemoveVacuum (completedPacketCycleTransfer order x) =
      completedPacketCycleTransfer order (completedRemoveVacuum x) := by
  induction order with
  | nil => rfl
  | cons l rest ih =>
      unfold completedPacketCycleTransfer
      rw [← completedRemoveVacuum_transfer_commute, ih]

private theorem stagedRemove_stagePacket_eq_of_vacuumFree {N : Nat}
    (P : CharacterPacket N) (hP : coeffAt P 0 ≈ 0) :
    StagedEqv (stagedRemoveVacuum (stagePacket P)) (stagePacket P) := by
  intro s
  by_cases hs : s = 0
  · subst s
    refine Q'.eqv_trans _ 0 _ (by
      simpa using coeffAt_stagedRemoveVacuum (stagePacket P) 0) ?_
    exact Q'.eqv_symm hP
  · simpa [hs] using coeffAt_stagedRemoveVacuum (stagePacket P) s

/-- A finite vacuum-free packet embeds directly into the range of the
completed excited projector. -/
theorem completedRemoveVacuum_embed_vacuumFree {N : Nat}
    (P : CharacterPacket N) (hP : coeffAt P 0 ≈ 0) :
    completedRemoveVacuum (embedV packetColimitGNS (stagePacket P)) =
      embedV packetColimitGNS (stagePacket P) := by
  refine Eq.trans (completedRemoveVacuum_embed (stagePacket P)) ?_
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS
      (stagedRemove_stagePacket_eq_of_vacuumFree P hP))

/-- Every iterate of a vacuum-free finite packet remains in the same
completed excited range. -/
theorem completedRemoveVacuum_packetCycleTransfer_vacuumFree {N : Nat}
    (order : List Nat) (P : CharacterPacket N)
    (hP : coeffAt P 0 ≈ 0) :
    completedRemoveVacuum
        (completedPacketCycleTransfer order
          (embedV packetColimitGNS (stagePacket P))) =
      completedPacketCycleTransfer order
        (embedV packetColimitGNS (stagePacket P)) := by
  rw [completedRemoveVacuum_cycle_commute,
    completedRemoveVacuum_embed_vacuumFree P hP]

/-- On a nonempty cycle, the outermost physical link has the sharp completed
`1/8` norm edge, and its input is canonically projected. -/
theorem completedPacketCycleTransfer_projected_outer_edge
    (l : Nat) (rest : List Nat)
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x))
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x)))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedPacketCycleTransfer rest
            (completedRemoveVacuum x)))
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedPacketCycleTransfer rest
            (completedRemoveVacuum x)))) := by
  have hfixed : completedRemoveVacuum
      (completedPacketCycleTransfer rest (completedRemoveVacuum x)) =
      completedPacketCycleTransfer rest (completedRemoveVacuum x) := by
    rw [completedRemoveVacuum_cycle_commute,
      completedRemoveVacuum_idempotent]
  simpa [completedPacketCycleTransfer, hfixed] using
    completedPacketTransfer_projected_edge
      (completedPacketCycleTransfer rest (completedRemoveVacuum x))

end YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.coeffAt_packetCycleTransfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.packetCycleTransfer_eq_cycleTransferredPacket
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.packetCycleTransfer_vacuumFree
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedPacketCycleTransfer_embed
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedPacketCycleTransfer_eq_cycleTransferredPacket
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedRemoveVacuum_cycle_commute
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedRemoveVacuum_embed_vacuumFree
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedRemoveVacuum_packetCycleTransfer_vacuumFree
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer.completedPacketCycleTransfer_projected_outer_edge
