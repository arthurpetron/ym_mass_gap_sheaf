/-
# Volume-uniform completed gap in the common-label cycle sector

Every finite completed packet-cycle iterate is a contraction.  Combining
that fact with the sharp projected edge on one physical link gives a single
`1/8` norm factor (equivalently `1/64` in squared norm) relative to the
original projected state, independently of the number of links in the cycle.

This is the volume-uniform estimate for the bivalent common-label sector.
It is not yet a finite-lattice Yang--Mills gap: multi-vertex intertwiner
quotients and their global vacuum projection remain separate obligations.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer
import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap

set_option maxHeartbeats 800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.HamiltonianScalar.SmulGNSData
open YMGap.Continuum.SU2FiniteCharacterPacketColimitGNS
open YMGap.Continuum.SU2FiniteCharacterPacketColimitCompletedTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketColimitVacuumProjection
open YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleTransfer

private theorem RCscale_eq_of_eqv {a b : Q'} (hab : a.eqv b)
    (x : CReal.RC) : CReal.RCscale a x = CReal.RCscale b x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact CReal.mul_congr_left (CReal.ofQ'_equiv_of_eqv hab)

/-- Arbitrarily many completed physical packet transfers remain
nonexpansive. -/
theorem completedPacketCycleTransfer_contraction (order : List Nat)
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer order x)
        (completedPacketCycleTransfer order x))
      (packetColimitGNS.cinnerCompl x x) := by
  induction order with
  | nil => exact CReal.RCle_refl _
  | cons l rest ih =>
      exact CReal.RCle_trans
        (completedPacketTransfer_contraction
          (completedPacketCycleTransfer rest x)) ih

private theorem completed_smul_norm_mono (q : Q') (hq : (0 : Q') ≤ q)
    {x y : GNSCompletionSpace packetColimitGNS}
    (hxy : CReal.RCle (packetColimitGNS.cinnerCompl x x)
      (packetColimitGNS.cinnerCompl y y)) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul q x)
        (packetColimitSmulGNS.cSmul q x))
      (packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul q y)
        (packetColimitSmulGNS.cSmul q y)) := by
  change CReal.RCle
    (packetColimitSmulGNS.toGNSData.cinnerCompl
      (packetColimitSmulGNS.cSmul q x)
      (packetColimitSmulGNS.cSmul q x))
    (packetColimitSmulGNS.toGNSData.cinnerCompl
      (packetColimitSmulGNS.cSmul q y)
      (packetColimitSmulGNS.cSmul q y))
  rw [packetColimitSmulGNS.cinnerCompl_cSmul_left,
    packetColimitSmulGNS.cinnerCompl_cSmul_right,
    packetColimitSmulGNS.cinnerCompl_cSmul_left,
    packetColimitSmulGNS.cinnerCompl_cSmul_right]
  exact CReal.RCscale_mono hq (CReal.RCscale_mono hq hxy)

/-- The vector-side `1/8` scaling is exactly the `1/64` squared-norm scale. -/
theorem completed_eighth_smul_norm (x : GNSCompletionSpace packetColimitGNS) :
    packetColimitGNS.cinnerCompl
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth x)
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth x) =
      CReal.RCscale
        (SU2PeterWeylWilsonBlock.eighth *
          SU2PeterWeylWilsonBlock.eighth)
        (packetColimitGNS.cinnerCompl x x) := by
  change packetColimitSmulGNS.toGNSData.cinnerCompl
      (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth x)
      (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth x) = _
  rw [packetColimitSmulGNS.cinnerCompl_cSmul_left,
    packetColimitSmulGNS.cinnerCompl_cSmul_right,
    CReal.RCscale_RCscale]
  rfl

/-- A nonempty completed common-label cycle contracts every canonically
projected state by the same sharp squared-norm edge, with no dependence on
cycle length. -/
theorem completedPacketCycleTransfer_projected_uniform_edge
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
          (completedRemoveVacuum x))
        (packetColimitSmulGNS.cSmul SU2PeterWeylWilsonBlock.eighth
          (completedRemoveVacuum x))) := by
  exact CReal.RCle_trans
    (completedPacketCycleTransfer_projected_outer_edge l rest x)
    (completed_smul_norm_mono SU2PeterWeylWilsonBlock.eighth (by decide)
      (completedPacketCycleTransfer_contraction rest
        (completedRemoveVacuum x)))

/-- Equivalent scalar form of the volume-uniform edge, exposing the exact
squared separation constant `(1/8)^2 = 1/64`. -/
theorem completedPacketCycleTransfer_projected_uniform_squared_sep
    (l : Nat) (rest : List Nat)
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x))
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x)))
      (CReal.RCscale
        (SU2PeterWeylWilsonBlock.eighth *
          SU2PeterWeylWilsonBlock.eighth)
        (packetColimitGNS.cinnerCompl
          (completedRemoveVacuum x) (completedRemoveVacuum x))) := by
  rw [← completed_eighth_smul_norm]
  exact completedPacketCycleTransfer_projected_uniform_edge l rest x

/-- Numerically explicit form of the same uniform gap: the completed squared
norm is bounded by exactly `1/64` of the original projected squared norm. -/
theorem completedPacketCycleTransfer_projected_uniform_one_over_64
    (l : Nat) (rest : List Nat)
    (x : GNSCompletionSpace packetColimitGNS) :
    CReal.RCle
      (packetColimitGNS.cinnerCompl
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x))
        (completedPacketCycleTransfer (l :: rest)
          (completedRemoveVacuum x)))
      (CReal.RCscale (Q'.mkPos 1 64 (by decide))
        (packetColimitGNS.cinnerCompl
          (completedRemoveVacuum x) (completedRemoveVacuum x))) := by
  rw [← RCscale_eq_of_eqv
    (show (SU2PeterWeylWilsonBlock.eighth *
      SU2PeterWeylWilsonBlock.eighth).eqv
        (Q'.mkPos 1 64 (by decide)) by decide)]
  exact completedPacketCycleTransfer_projected_uniform_squared_sep l rest x

end YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap.completedPacketCycleTransfer_contraction
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap.completed_eighth_smul_norm
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap.completedPacketCycleTransfer_projected_uniform_edge
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap.completedPacketCycleTransfer_projected_uniform_squared_sep
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketCompletedCycleUniformGap.completedPacketCycleTransfer_projected_uniform_one_over_64
