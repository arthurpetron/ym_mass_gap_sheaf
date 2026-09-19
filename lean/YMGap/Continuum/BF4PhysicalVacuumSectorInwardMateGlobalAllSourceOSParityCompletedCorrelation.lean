/-
# The inward-mate parity correlation-square handoff in the completed carrier

The completed parity carrier already has an exact same-object coefficient.
This module combines that identity with completed Cauchy--Schwarz, the finite
Boolean norm bound, and transfer contraction.  It yields a genuine
same-object correlation-square estimate for the explicit parity vector.

The result is still one-vector data.  It is not an all-observable Poincare
inequality, a thermodynamic or continuum passage, or a Clay mass-gap theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The completed parity coefficient squared is bounded by the transferred
vector norm. -/
theorem globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_transferredNorm
    (K : Nat) :
    let w := anchorCoupling
    let hw : (0 : Q') ≤ w := by decide
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
    CReal.RCle
      (CReal.RCmul
        (physicalConstantRC
          (centralPhysicalJointQuadratic w hw K 0
            (globalInwardMateCenteredParity K)))
        (physicalConstantRC
          (centralPhysicalJointQuadratic w hw K 0
            (globalInwardMateCenteredParity K))))
      (D.cinnerCompl transferred transferred) := by
  dsimp only
  let w := anchorCoupling
  let hw : (0 : Q') ≤ w := by decide
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
  have hcs := D.RC_cauchy_schwarz vector transferred
  have hcoefficient := globalInwardMateCenteredParityCompletedObservable_sameObjectCoefficient K
  change D.cinnerCompl vector transferred = _ at hcoefficient
  rw [hcoefficient] at hcs
  have hnormRat := globalInwardMateCenteredParityWeightedSquare_le_one K
  have hnorm := physicalConstantRC_le_of_rat hnormRat
  change CReal.RCle (D.cinnerCompl vector vector) (physicalConstantRC 1) at hnorm
  have htransferred0 := D.cinner_self_nonneg transferred
  have hmul := physicalRCmul_mono_nonnegative_left htransferred0 hnorm
  rw [CReal.RCmul_comm (D.cinnerCompl vector vector)
      (D.cinnerCompl transferred transferred)] at hcs
  rw [physicalRCmul_constant_one_right] at hmul
  exact CReal.RCle_trans hcs hmul

/-- Transfer contraction upgrades the preceding estimate to the original
parity norm. -/
theorem globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_norm
    (K : Nat) :
    let w := anchorCoupling
    let hw : (0 : Q') ≤ w := by decide
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    CReal.RCle
      (CReal.RCmul
        (physicalConstantRC
          (centralPhysicalJointQuadratic w hw K 0
            (globalInwardMateCenteredParity K)))
        (physicalConstantRC
          (centralPhysicalJointQuadratic w hw K 0
            (globalInwardMateCenteredParity K))))
      (D.cinnerCompl vector vector) := by
  dsimp only
  let w := anchorCoupling
  let hw : (0 : Q') ≤ w := by decide
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
  exact CReal.RCle_trans
    (globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_transferredNorm K)
    (centralPhysicalCompletedMarkovTransfer_contraction w hw K 0 vector)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_transferredNorm
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_norm
