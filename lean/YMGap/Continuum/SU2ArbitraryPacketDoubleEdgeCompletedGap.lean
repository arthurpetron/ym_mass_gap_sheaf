/-
# Completed projected gap after the simultaneous double-edge quotient

The simultaneous two-edge quotient between trivalent vertices cannot be
replaced by two independent edge contractions: the all-fundamental graph is
killed by the joint parity constraint.  This module connects the correct
joint quotient to the completed packet GNS transfer and its exact projected
spectral edge.

For arbitrary incident packets, association, endpoint orientation, and six
independent cutoff enlargements remain invisible after the canonical global
vacuum projection and one physical transfer.  Every projected joint state
then contracts in squared norm by at most exactly `1/64`.

The estimate is non-vacuous and sharp on an explicit graph: take the two
shared legs at each endpoint in the fundamental character and the external
leg in the vacuum character.  The joint quotient has only the retained
fundamental mode, with coefficient `1/8`; its Wilson norm is `1/512`, and one
physical transfer changes the norm to `1/32768 = (1/64)(1/512)`.

Honest scope: this is the completed gap for the smallest simultaneous
two-edge quotient.  It does not yet assemble arbitrary finite spin networks
or a thermodynamic/continuum limit.
-/

import YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient
import YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap

namespace YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
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
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeJointQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem embedV_eq_of_packetEqv {K : Nat}
    {P Q : CharacterPacket K} (h : PacketEqv P Q) :
    embedV packetColimitGNS (stagePacket P) =
      embedV packetColimitGNS (stagePacket Q) := by
  apply Quotient.sound
  exact embed_null_of_rad packetColimitGNS
    (rad_of_veq packetColimitGNS (fun s => coeffAt_packetEqv h s))

/-! ## Arbitrary joint states: projection and one-link transfer -/

/-- The correct simultaneous two-edge quotient, followed by the canonical
global vacuum projection in the all-character completed packet GNS space. -/
def completedArbitraryDoubleEdgeProjectedState
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    GNSCompletionSpace packetColimitGNS :=
  completedRemoveVacuum
    (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂)

/-- The projected joint state is in the exact range of the canonical excited
projection. -/
theorem completedArbitraryDoubleEdgeProjectedState_fixed
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedRemoveVacuum
        (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂ := by
  exact completedRemoveVacuum_idempotent _

/-- Local association changes do not change the projected completed state. -/
theorem completedArbitraryDoubleEdgeProjected_association
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      completedRemoveVacuum
        (completedArbitraryDoubleEdgeCyclicState P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  congrArg completedRemoveVacuum
    (completedArbitraryDoubleEdge_association P₁ Q₁ R₁ P₂ Q₂ R₂)

/-- Reversing both shared edges does not change the projected completed
state. -/
theorem completedArbitraryDoubleEdgeProjected_orientation
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂ =
      completedRemoveVacuum
        (completedArbitraryDoubleEdgeOrientationReverseState
          P₁ Q₁ R₁ P₂ Q₂ R₂) :=
  congrArg completedRemoveVacuum
    (completedArbitraryDoubleEdge_orientation P₁ Q₁ R₁ P₂ Q₂ R₂)

/-- Six unrelated cutoff enlargements remain invisible after the joint
quotient and global vacuum projection. -/
theorem completedArbitraryDoubleEdgeProjected_pad_independent
    {N₁ N₁' M₁ M₁' L₁ L₁' N₂ N₂' M₂ M₂' L₂ L₂' : Nat}
    (hN₁ : N₁ ≤ N₁') (hM₁ : M₁ ≤ M₁') (hL₁ : L₁ ≤ L₁')
    (hN₂ : N₂ ≤ N₂') (hM₂ : M₂ ≤ M₂') (hL₂ : L₂ ≤ L₂')
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedArbitraryDoubleEdgeProjectedState
        (padPacket hN₁ P₁) (padPacket hM₁ Q₁) (padPacket hL₁ R₁)
        (padPacket hN₂ P₂) (padPacket hM₂ Q₂) (padPacket hL₂ R₂) =
      completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂ :=
  congrArg completedRemoveVacuum
    (completedArbitraryDoubleEdge_pad_independent
      hN₁ hM₁ hL₁ hN₂ hM₂ hL₂ P₁ Q₁ R₁ P₂ Q₂ R₂)

/-- One genuine physical packet transfer commutes with forming the canonical
global excited part of the joint quotient. -/
theorem completedArbitraryDoubleEdgeProjected_transfer_commutes
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    completedPacketTransfer
        (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂) =
      completedRemoveVacuum
        (completedPacketTransfer
          (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂)) := by
  exact completedRemoveVacuum_transfer_commute _

/-- **Uniform completed joint-quotient gap.**  After the simultaneous shared
label/intertwiner quotient and the canonical global vacuum projection, one
physical link contracts squared norm by exactly the same `1/64` upper factor
as the full one-link character sector.  The constant is independent of all
six packet cutoffs. -/
theorem completedArbitraryDoubleEdgeProjected_uniform_one_over_64
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketTransfer
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂))
        (completedPacketTransfer
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂)))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂)
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂))) := by
  simpa [completedPacketCycleTransfer,
    completedArbitraryDoubleEdgeProjectedState,
    completedRemoveVacuum_idempotent] using
      (completedPacketCycleTransfer_projected_uniform_one_over_64
        0 []
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂))

/-- The same exact squared-norm edge survives an arbitrary nonempty finite
sequence of physical link transfers after the simultaneous quotient.  Extra
links are merely contractive, so the bound is independent of their number. -/
theorem completedArbitraryDoubleEdgeProjected_cycle_uniform_one_over_64
    {N₁ M₁ L₁ N₂ M₂ L₂ : Nat}
    (l : Nat) (rest : List Nat)
    (P₁ : CharacterPacket N₁) (Q₁ : CharacterPacket M₁)
    (R₁ : CharacterPacket L₁) (P₂ : CharacterPacket N₂)
    (Q₂ : CharacterPacket M₂) (R₂ : CharacterPacket L₂) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer (l :: rest)
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂))
        (completedPacketCycleTransfer (l :: rest)
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂)))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂)
          (completedArbitraryDoubleEdgeProjectedState P₁ Q₁ R₁ P₂ Q₂ R₂))) := by
  simpa [completedArbitraryDoubleEdgeProjectedState,
    completedRemoveVacuum_idempotent] using
      (completedPacketCycleTransfer_projected_uniform_one_over_64
        l rest
        (completedArbitraryDoubleEdgeJointState P₁ Q₁ R₁ P₂ Q₂ R₂))

/-! ## A sharp nonzero simultaneous-quotient witness -/

/-- The all-fundamental simultaneous quotient vanishes coefficientwise, not
merely after taking its scalar Gram.  This is the carrier-level form of the
parity fence `N₁₁¹ = 0`. -/
theorem fundamentalDoubleEdgeJointPacket_zero :
    PacketEqv
      (doubleEdgeJointPacket doubleEdgeFundamental doubleEdgeFundamental
        doubleEdgeFundamental doubleEdgeFundamental doubleEdgeFundamental
        doubleEdgeFundamental)
      (zeroPacket 1) := by
  intro i
  refine Fin.cases (by decide) ?_ i
  intro j
  refine Fin.cases (by decide) ?_ j
  intro k
  exact Fin.elim0 k

/-- Consequently the all-fundamental graph is literally the zero vector in
the completed GNS carrier after the correct simultaneous quotient. -/
theorem completedFundamentalDoubleEdgeJointState_zero :
    completedDoubleEdgeJointState doubleEdgeFundamental doubleEdgeFundamental
        doubleEdgeFundamental doubleEdgeFundamental doubleEdgeFundamental
        doubleEdgeFundamental =
      embedV packetColimitGNS (stagePacket (zeroPacket 1)) :=
  embedV_eq_of_packetEqv fundamentalDoubleEdgeJointPacket_zero

/-- Vacuum external leg at cutoff one. -/
def doubleEdgeVacuumExternal : CharacterPacket 1 := vacuumPacket 1

/-- Two fundamental shared legs and one vacuum external leg at each endpoint.
The simultaneous quotient is nonzero and supported on the retained
fundamental label. -/
def fundamentalVacuumDoubleEdgePacket : CharacterPacket 1 :=
  doubleEdgeJointPacket doubleEdgeFundamental doubleEdgeFundamental
    doubleEdgeVacuumExternal doubleEdgeFundamental doubleEdgeFundamental
    doubleEdgeVacuumExternal

/-- The retained vacuum coefficient vanishes exactly. -/
theorem fundamentalVacuumDoubleEdgePacket_zero :
    coeffAt fundamentalVacuumDoubleEdgePacket 0 ≈ 0 := by decide

/-- The retained fundamental coefficient is exactly `1/8`: the second common
fundamental edge contributes its physical Wilson eigenvalue. -/
theorem fundamentalVacuumDoubleEdgePacket_one :
    coeffAt fundamentalVacuumDoubleEdgePacket 1 ≈
      Q'.mkPos 1 8 (by decide) := by decide

/-- Exact interacting Wilson squared norm of the nonzero joint packet. -/
theorem fundamentalVacuumDoubleEdgePacket_norm_exact :
    packetWilsonGram fundamentalVacuumDoubleEdgePacket
      fundamentalVacuumDoubleEdgePacket ≈
        Q'.mkPos 1 512 (by decide) := by decide

/-- Exact squared norm after one physical transfer. -/
theorem fundamentalVacuumDoubleEdgePacket_transfer_norm_exact :
    packetWilsonGram (packetTransfer fundamentalVacuumDoubleEdgePacket)
      (packetTransfer fundamentalVacuumDoubleEdgePacket) ≈
        Q'.mkPos 1 32768 (by decide) := by decide

/-- **Sharpness witness.**  The nonzero simultaneous joint quotient attains
the completed estimate's exact squared-norm factor `1/64`. -/
theorem fundamentalVacuumDoubleEdgePacket_sharp_one_over_64 :
    packetWilsonGram (packetTransfer fundamentalVacuumDoubleEdgePacket)
        (packetTransfer fundamentalVacuumDoubleEdgePacket) ≈
      Q'.mkPos 1 64 (by decide) *
        packetWilsonGram fundamentalVacuumDoubleEdgePacket
          fundamentalVacuumDoubleEdgePacket := by decide

end YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap

#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjectedState_fixed
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_association
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_orientation
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_pad_independent
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_transfer_commutes
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_uniform_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedArbitraryDoubleEdgeProjected_cycle_uniform_one_over_64
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalDoubleEdgeJointPacket_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.completedFundamentalDoubleEdgeJointState_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalVacuumDoubleEdgePacket_zero
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalVacuumDoubleEdgePacket_one
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalVacuumDoubleEdgePacket_norm_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalVacuumDoubleEdgePacket_transfer_norm_exact
#print axioms YMGap.Continuum.SU2ArbitraryPacketDoubleEdgeCompletedGap.fundamentalVacuumDoubleEdgePacket_sharp_one_over_64
