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

private theorem rc_deficit_lower
    (rate : Q') (norm form : CReal.RC)
    (h : CReal.RCle form (CReal.RCscale rate norm)) :
    CReal.RCle
      (CReal.RCscale (1 + -rate) norm)
      (CReal.RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon hepsilon
  obtain ⟨index, hN⟩ := h epsilon hepsilon
  refine ⟨index, fun n hn => ?_⟩
  have hf := hN n hn
  change F.approx n ≤ rate * N.approx n + epsilon at hf
  have hneg := Q'.neg_le_neg_add hf
  have hsum := Q'.add_le_add_left (N.approx n) _ _ hneg
  change (1 + -rate) * N.approx n ≤
    (N.approx n + -(F.approx n)) + epsilon
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-rate) (N.approx n))
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv (N.approx n))
          (Q'.neg_mul_eqv rate (N.approx n)))))
    (Q'.le_trans' _ _ _ hsum
      (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

private theorem physicalConstantRC_mul_eq_scale (factor value : Q') :
    physicalConstantRC (factor * value) =
      CReal.RCscale factor (physicalConstantRC value) := by
  apply Quotient.sound
  exact YMGap.Constructive.CRealAlg.ofQ'_mul factor value

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

/-- The concrete parity same-object coefficient is nonnegative because the
completed physical Markov transfer is positive and self-adjoint. -/
theorem globalInwardMateCenteredParityCompletedObservable_coefficient_nonnegative
    (K : Nat) :
    let w := anchorCoupling
    let hw : (0 : Q') ≤ w := by decide
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    CReal.RCnonneg
      (D.cinnerCompl vector
        (centralPhysicalCompletedMarkovTransfer w hw K 0 vector)) := by
  dsimp only
  let w := anchorCoupling
  let hw : (0 : Q') ≤ w := by decide
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  have hpositive := centralPhysicalCompletedMarkovTransfer_positive
    w hw K 0 vector
  rw [centralPhysicalCompletedMarkovTransfer_selfAdjoint] at hpositive
  exact hpositive

/-- Transfer contraction upgrades Cauchy--Schwarz to the usual squared
same-object coefficient bound by the original completed norm square. -/
theorem globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_normSquare
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
      (CReal.RCmul (D.cinnerCompl vector vector)
        (D.cinnerCompl vector vector)) := by
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
  have hcontract := centralPhysicalCompletedMarkovTransfer_contraction
    w hw K 0 vector
  have hnorm := D.cinner_self_nonneg vector
  have hmul := physicalRCmul_mono_nonnegative_left hnorm hcontract
  exact CReal.RCle_trans hcs hmul

/-- The finite parity margin becomes a completed Rayleigh-deficit estimate for
the same completed vector. -/
theorem globalInwardMateCenteredParityCompletedObservable_margin_mul_norm_le_deficit
    (K : Nat) (hK : 1 <= K) :
    let w := anchorCoupling
    let hw : (0 : Q') ≤ w := by decide
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
    CReal.RCle
      (CReal.RCscale globalInwardMateParityFormMargin
        (D.cinnerCompl vector vector))
      (CReal.RCsub
        (D.cinnerCompl vector vector)
        (D.cinnerCompl vector transferred)) := by
  dsimp only
  let w := anchorCoupling
  let hw : (0 : Q') ≤ w := by decide
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
  have hstrict := globalInwardMateCenteredParityCompletedObservable_strict_form K hK
  dsimp only at hstrict
  rw [centralPhysicalCompletedMarkovTransfer_selfAdjoint] at hstrict
  exact rc_deficit_lower globalInwardMateParityFormRate
    (D.cinnerCompl vector vector) (D.cinnerCompl vector transferred) hstrict

/-- The completed parity vector has a strictly positive same-object Rayleigh
deficit, witnessed constructively by the square of the finite margin. -/
theorem globalInwardMateCenteredParityCompletedObservable_deficit_positive
    (K : Nat) (hK : 1 <= K) :
    let w := anchorCoupling
    let hw : (0 : Q') ≤ w := by decide
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
    YMGap.Continuum.RCStrictPositivity.RCIsPositive
      (CReal.RCsub
        (D.cinnerCompl vector vector)
        (D.cinnerCompl vector transferred)) := by
  dsimp only
  let w := anchorCoupling
  let hw : (0 : Q') ≤ w := by decide
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
  have hmargin := globalInwardMateParityFormMargin_positive
  have hfloor := globalInwardMateCenteredParityCompletedObservable_norm_floor K hK
  have hscale := CReal.RCscale_mono
    (Q'.le_of_lt hmargin) hfloor
  have hscaledFloor :
      CReal.RCle
        (physicalConstantRC
          (globalInwardMateParityFormMargin *
            globalInwardMateParityFormMargin))
        (CReal.RCscale globalInwardMateParityFormMargin
          (D.cinnerCompl vector vector)) := by
    exact CReal.RCle_trans
      (CReal.RCle_refl
        (CReal.RCscale globalInwardMateParityFormMargin
          (physicalConstantRC globalInwardMateParityFormMargin)))
      hscale
  rw [physicalConstantRC_mul_eq_scale] at hscaledFloor
  refine ⟨globalInwardMateParityFormMargin * globalInwardMateParityFormMargin,
    Q'.mul_pos hmargin hmargin, ?_⟩
  exact CReal.RCle_trans hscaledFloor
    (globalInwardMateCenteredParityCompletedObservable_margin_mul_norm_le_deficit
      K hK)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_transferredNorm
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_norm
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_coefficient_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_correlationSquare_le_normSquare
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_margin_mul_norm_le_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCorrelation.globalInwardMateCenteredParityCompletedObservable_deficit_positive
