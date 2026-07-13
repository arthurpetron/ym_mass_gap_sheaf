/-
# Transporting the finite O(4)-response packet through shared-link fusion

The smallest shared-link block has four redundant pre-fusion coordinates and
three physical quotient coordinates `(chi_0, chi_1, chi_2)`.  The existing
finite Wilson-packet response at cutoff two has exactly those three channels,
but that identification was previously only prose.

This module makes the identification constructive.  It builds the quotient
packet from the actual shared-link fusion coordinates, gives an explicit
section back to the redundant four-coordinate block, proves both quotient
surjectivity and compatibility with the physical heat-kernel transfer, and
then transports the quarter-turn response and limiting invariance to four
directional copies of the shared-link block.

Honest scope: this closes the response transport for one fused shared link.
It does not glue the quotient sections consistently around a multi-link
plaquette network, where the already checked bigon vacuum-screening
obstruction must still be projected globally.  Nor does a lattice
quarter-turn supply the continuum family of physical O(4) rotations.
-/

import YMGap.Continuum.SU2SharedLinkFusionBlock
import YMGap.Continuum.SU2FiniteCharacterPacketO4Response

namespace YMGap.Continuum.SU2SharedLinkFusionO4Response

set_option maxHeartbeats 600000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketO4Response
open YMGap.Continuum.SU2SharedLinkFusionBlock

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               zero_num_cast, zero_den_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## 1. The exact cutoff-two packet of a fused shared link -/

/-- The three physical quotient coordinates of the shared-link block,
packaged as the cutoff-two character packet. -/
def fusedPacket (a : SharedVec) : CharacterPacket 2 where
  coeff i :=
    if i.val = 0 then vacuumCoord a
    else if i.val = 1 then fundamentalCoord a
    else quadraticCoord a

theorem fusedPacket_coeff_zero (a : SharedVec) :
    (fusedPacket a).coeff ⟨0, by decide⟩ = vacuumCoord a := by
  rfl

theorem fusedPacket_coeff_one (a : SharedVec) :
    (fusedPacket a).coeff ⟨1, by decide⟩ = fundamentalCoord a := by
  rfl

theorem fusedPacket_coeff_two (a : SharedVec) :
    (fusedPacket a).coeff ⟨2, by decide⟩ = quadraticCoord a := by
  rfl

/-- A constructive section of the fusion quotient.  The subtraction in the
vacuum input compensates the vacuum copy inside `chi_1^2 = chi_0 + chi_2`. -/
def fusionSection (P : CharacterPacket 2) : SharedVec :=
  (P.coeff ⟨0, by decide⟩ + (-P.coeff ⟨2, by decide⟩),
    (P.coeff ⟨1, by decide⟩, (0, P.coeff ⟨2, by decide⟩)))

/-- The section recovers all three quotient coordinates exactly in the `Q'`
setoid. -/
theorem fusionCollapse_section (P : CharacterPacket 2) :
    IrrepEq (fusionCollapse (fusionSection P))
      (P.coeff ⟨0, by decide⟩,
        (P.coeff ⟨1, by decide⟩, P.coeff ⟨2, by decide⟩)) := by
  let p0 := P.coeff ⟨0, by decide⟩
  let p1 := P.coeff ⟨1, by decide⟩
  let p2 := P.coeff ⟨2, by decide⟩
  change IrrepEq ((p0 + (-p2)) + p2, (p1 + 0, p2)) (p0, (p1, p2))
  refine ⟨?_, ?_, Q'.eqv_refl p2⟩
  · refine Q'.eqv_trans _ (p0 + ((-p2) + p2)) _
      (Q'.add_assoc_eqv p0 (-p2) p2) ?_
    refine Q'.eqv_trans _ (p0 + 0) _
      (Q'.add_eqv_congr_left p0 _ _ (Q'.neg_add_self_eqv p2)) ?_
    exact QPoly.q_add_zero_eqv p0
  · exact QPoly.q_add_zero_eqv p1

/-- Every cutoff-two character packet is in the image of the actual
shared-link quotient.  This is data-level surjectivity via `fusionSection`,
not a choice argument. -/
theorem fusedPacket_section (P : CharacterPacket 2) :
    PacketEqv (fusedPacket (fusionSection P)) P := by
  intro i
  have hcollapse := fusionCollapse_section P
  by_cases h0 : i.val = 0
  · have hi : i = (⟨0, by decide⟩ : Fin 3) := Fin.ext h0
    subst i
    exact hcollapse.1
  · by_cases h1 : i.val = 1
    · have hi : i = (⟨1, by decide⟩ : Fin 3) := Fin.ext h1
      subst i
      exact hcollapse.2.1
    · have h2 : i.val = 2 := by omega
      have hi : i = (⟨2, by decide⟩ : Fin 3) := Fin.ext h2
      subst i
      exact hcollapse.2.2

/-- The cutoff-two packet eigenvalue on the quadratic channel is literally
the shared-link quadratic eigenvalue. -/
theorem packetEigen_two_eq_quadratic :
    packetEigen 2 = quadraticEigen := rfl

/-- Shared-link fusion commutes with the physical heat-kernel transfer on all
three quotient channels. -/
theorem fusedPacket_transfer_intertwiner (a : SharedVec) :
    PacketEqv (fusedPacket (sharedTransfer a))
      (packetTransfer (fusedPacket a)) := by
  intro i
  by_cases h0 : i.val = 0
  · have hi : i = (⟨0, by decide⟩ : Fin 3) := Fin.ext h0
    subst i
    exact Q'.eqv_trans _ _ _
      (sharedTransfer_vacuum_coord a)
      (Q'.eqv_symm (Q'.one_mul_eqv (vacuumCoord a)))
  · by_cases h1 : i.val = 1
    · have hi : i = (⟨1, by decide⟩ : Fin 3) := Fin.ext h1
      subst i
      exact Q'.eqv_trans _
        (SU2PeterWeylWilsonBlock.eighth * fundamentalCoord a) _
        (sharedTransfer_fundamental_coord a)
        (Q'.eqv_symm
          (Q'.mul_eqv_congr_right _ _ _ packetEigen_one))
    · have h2 : i.val = 2 := by omega
      have hi : i = (⟨2, by decide⟩ : Fin 3) := Fin.ext h2
      subst i
      exact sharedTransfer_quadratic_coord a

/-! ## 2. Four directional shared-link blocks -/

structure SharedDir4 where
  east : SharedVec
  north : SharedVec
  west : SharedVec
  south : SharedVec

/-- Fuse each directional shared-link block into its three physical channels. -/
def fuseDirections (o : SharedDir4) : PacketDir4 2 :=
  ⟨fusedPacket o.east, fusedPacket o.north,
    fusedPacket o.west, fusedPacket o.south⟩

/-- Literal lattice quarter-turn before taking the fusion quotient. -/
def sharedQuarterTurn (o : SharedDir4) : SharedDir4 :=
  ⟨o.south, o.east, o.north, o.west⟩

theorem fuseDirections_quarterTurn (o : SharedDir4) :
    fuseDirections (sharedQuarterTurn o) =
      (packetQuarterTurnHom 2).map (fuseDirections o) := rfl

/-- Apply the explicit one-link quotient section in each direction. -/
def directionSection (o : PacketDir4 2) : SharedDir4 :=
  ⟨fusionSection o.east, fusionSection o.north,
    fusionSection o.west, fusionSection o.south⟩

def PacketDir4Eqv (a b : PacketDir4 2) : Prop :=
  PacketEqv a.east b.east /\ PacketEqv a.north b.north /\
    PacketEqv a.west b.west /\ PacketEqv a.south b.south

/-- Every four-direction cutoff-two packet has a constructive preimage in
four copies of the actual shared-link fusion block. -/
theorem fuseDirections_section (o : PacketDir4 2) :
    PacketDir4Eqv (fuseDirections (directionSection o)) o :=
  ⟨fusedPacket_section o.east, fusedPacket_section o.north,
    fusedPacket_section o.west, fusedPacket_section o.south⟩

/-- The exact same-state response theorem, now with its observable supplied
by four shared-link fusion blocks before quotienting. -/
theorem sharedFusionQuarterTurn_same_state_response
    (o : SharedDir4) (j : Nat) :
    ((packetDir4Scaling 2).atSpacing j).E
        (fuseDirections (sharedQuarterTurn o)) ≤
      ((packetDir4Scaling 2).atSpacing j).E (fuseDirections o) +
        packetDir4Response (fuseDirections o) *
          O4RestorationAF.breakCoeff
            O4ObservableSymmetryBridge.halfScalingDecay j
    /\
    ((packetDir4Scaling 2).atSpacing j).E (fuseDirections o) ≤
      ((packetDir4Scaling 2).atSpacing j).E
          (fuseDirections (sharedQuarterTurn o)) +
        packetDir4Response (fuseDirections o) *
          O4RestorationAF.breakCoeff
            O4ObservableSymmetryBridge.halfScalingDecay j := by
  rw [fuseDirections_quarterTurn]
  exact packetQuarterTurn_same_state_response 2 (fuseDirections o) j

/-- Exact selected quarter-turn invariance in the constructive spacing limit
for every four-direction shared-link input. -/
theorem sharedFusion_limit_quarterTurn_invariant (o : SharedDir4) :
    RegularCReal.Equiv
      (RegularLinearScalingLimit.limitE (packetDir4Scaling 2)
        (fuseDirections (sharedQuarterTurn o)))
      (RegularLinearScalingLimit.limitE (packetDir4Scaling 2)
        (fuseDirections o)) := by
  rw [fuseDirections_quarterTurn]
  exact packetDir4_limit_quarterTurn_invariant 2 (fuseDirections o)

end YMGap.Continuum.SU2SharedLinkFusionO4Response

#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.fusionCollapse_section
#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.fusedPacket_section
#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.fusedPacket_transfer_intertwiner
#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.fuseDirections_section
#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.sharedFusionQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2SharedLinkFusionO4Response.sharedFusion_limit_quarterTurn_invariant
