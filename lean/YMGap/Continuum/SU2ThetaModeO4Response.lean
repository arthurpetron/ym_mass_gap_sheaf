/-
# Same-state O(4) response for the genuine wired theta mode

The trivalent shared-link construction already supplies a nonzero globally
projected theta spin network, together with its exact interacting Wilson
weight.  This file uses that weight as the positive partition of the
one-mode spectral algebra and transports the finite quarter-turn response to
four directional copies of the SAME theta state.

The positivity witness is derived from the exact identity
`pureQuadratic_thetaGram_exact`; no independently normalized link state is
substituted.  Thus the state used by the response has both trivalent endpoint
projectors imposed before normalization.

Honest scope: only the single retained spin-one theta mode is treated here.
The simultaneous multi-mode trivalent quotient, compatibility between
overlapping cells, and continuum physical rotations remain open.
-/

import YMGap.Continuum.SU2BivalentCycleO4Response
import YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

namespace YMGap.Continuum.SU2ThetaModeO4Response

set_option maxHeartbeats 900000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketO4Response
open YMGap.Continuum.SU2BivalentCycleO4Response
open YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

local infix:50 " ≈ " => Q'.eqv

/-! ## The exact positive theta partition -/

theorem thetaSpinOneTransferEigen_pos :
    (0 : Q') < thetaSpinOneTransferEigen := by
  unfold thetaSpinOneTransferEigen packetEigen
    SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling
  decide

theorem thetaSpinOneWiredGram_pos :
    (0 : Q') <
      thetaWiredWilsonGram pureQuadraticThetaLinks
        pureQuadraticThetaLinks := by
  exact Q'.pos_of_lt_of_le thetaSpinOneTransferEigen_pos
    (Q'.ge_of_eqv pureQuadratic_thetaGram_exact)

theorem thetaSpinOneWeight_partition_pos :
    (0 : Q') < fsum thetaSpinOneWeight 1 := by
  change (0 : Q') < 0 + thetaSpinOneWeight 0
  exact Q'.pos_of_lt_of_le thetaSpinOneWiredGram_pos
    (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _))

/-- The one coordinate is a relabeling of the retained spin-one theta mode;
its weight is the actual two-vertex-projected theta Wilson Gram. -/
def thetaSpinOnePositiveWeight : PositivePacketWeight 0 where
  weight := thetaSpinOneWeight
  weight_nonneg := thetaSpinOneWeight_nonneg
  partition_pos := thetaSpinOneWeight_partition_pos

theorem thetaSpinOneWeight_partition_is_wired_state :
    fsum thetaSpinOnePositiveWeight.weight 1 ≈
      thetaWiredWilsonGram pureQuadraticThetaLinks
        pureQuadraticThetaLinks := by
  change (0 + thetaSpinOneWeight 0) ≈
    thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks
  unfold thetaSpinOneWeight
  exact QPoly.q_zero_add_eqv _

theorem thetaSpinOneFunctional_normalized :
    (weightedPacketFunctional thetaSpinOnePositiveWeight).E
        (spectralOne 0) ≈ 1 :=
  (weightedPacketFunctional thetaSpinOnePositiveWeight).normalized

/-! ## Four directional copies and their exact quarter-turn response -/

/-- Same-state quarter-turn response for arbitrary observables of four
directional copies of the globally wired theta mode. -/
theorem thetaSpinOneQuarterTurn_same_state_response
    (o : PacketDir4 0) (j : Nat) :
    ((weightedDir4Scaling thetaSpinOnePositiveWeight).atSpacing j).E
        ((packetQuarterTurnHom 0).map o) ≤
      ((weightedDir4Scaling thetaSpinOnePositiveWeight).atSpacing j).E o +
        weightedDir4Response thetaSpinOnePositiveWeight o *
          breakCoeff halfScalingDecay j
    /\
    ((weightedDir4Scaling thetaSpinOnePositiveWeight).atSpacing j).E o ≤
      ((weightedDir4Scaling thetaSpinOnePositiveWeight).atSpacing j).E
          ((packetQuarterTurnHom 0).map o) +
        weightedDir4Response thetaSpinOnePositiveWeight o *
          breakCoeff halfScalingDecay j :=
  weightedQuarterTurn_same_state_response thetaSpinOnePositiveWeight o j

theorem thetaSpinOne_limit_quarterTurn_invariant (o : PacketDir4 0) :
    RegularCReal.Equiv
      (limitE (weightedDir4Scaling thetaSpinOnePositiveWeight)
        ((packetQuarterTurnHom 0).map o))
      (limitE (weightedDir4Scaling thetaSpinOnePositiveWeight) o) :=
  weightedDir4_limit_quarterTurn_invariant thetaSpinOnePositiveWeight o

end YMGap.Continuum.SU2ThetaModeO4Response

#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOneWiredGram_pos
#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOnePositiveWeight
#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOneWeight_partition_is_wired_state
#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOneFunctional_normalized
#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOneQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2ThetaModeO4Response.thetaSpinOne_limit_quarterTurn_invariant
