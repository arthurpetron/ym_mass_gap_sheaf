/-
# Inward-mate Poincare data on the concrete completed physical carrier

`GlobalInwardMateUniformPoincareCertificate` is a finite, uniform
mean-zero form estimate for the literal anchor-coupling BF4 transfer.  The
generic symmetric-reference completion bridge already knows how to pass such
an estimate to the actual completed GNS carrier.  This module makes that
connection explicit and exposes the resulting operator and same-object power
consequences.

The endpoint-coverage certificate remains an analytic input: no coverage
inhabitant, thermodynamic limit, continuum QFT, or Clay mass-gap theorem is
constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSymmetricReferenceCompletedGap
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSymmetricReferenceCompletedGap
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Finite form bound on the concrete anchor carrier -/

/-- The all-source inward-mate Poincare certificate is exactly the finite
quadratic-gap interface consumed by the constructive completion theorem. -/
def globalInwardMateUniformPoincare_finiteQuadraticGap
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (certificate : GlobalInwardMateUniformPoincareCertificate coverage)
    (K : Nat) (hK : 1 ≤ K) :
    CentralPhysicalFiniteQuadraticGapAtRate
      anchorCoupling (by decide) K 0 certificate.rate := by
  intro observable hmean
  have hmarkov := certificate.strict_form K hK observable hmean
  have hjoint :=
    centralPhysicalWeightedMarkovQuadratic_eq_joint
      anchorCoupling (by decide) K 0 observable
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hjoint)))
    hmarkov

/-- The finite inward-mate rate reaches the completed physical vacuum-form
contract at every cutoff covered by the certificate. -/
def globalInwardMateUniformPoincare_completed_vacuum_form_gap
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (certificate : GlobalInwardMateUniformPoincareCertificate coverage)
    (K : Nat) (hK : 1 ≤ K) :
    CentralPhysicalCompletedVacuumFormGap
      anchorCoupling (by decide) K 0 certificate.rate :=
  centralPhysicalCompletedVacuumFormGapData_of_finiteGapAtRate
    (by decide) K 0 certificate.rate_nonnegative certificate.rate_lt_one
    (globalInwardMateUniformPoincare_finiteQuadraticGap
      coverage certificate K hK)

/-! ## 2. Completed transfer and same-object consequences -/

/-- The concrete completed physical transfer obeys the squared inward-mate
rate on every vacuum-orthogonal vector. -/
theorem globalInwardMateUniformPoincare_completed_operator_norm_gap
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (certificate : GlobalInwardMateUniformPoincareCertificate coverage)
    (K : Nat) (hK : 1 ≤ K)
    (vector : CentralPhysicalGNSCompletion
      anchorCoupling (by decide) K 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      anchorCoupling (by decide) K 0 vector) :
    let rate := certificate.rate
    let D := (centralPhysicalSmulGNS
      anchorCoupling (by decide) K 0).toGNSData
    let transferred := centralPhysicalCompletedMarkovTransfer
      anchorCoupling (by decide) K 0 vector
    CReal.RCle
      (D.cinnerCompl transferred transferred)
      (CReal.RCscale (rate * rate)
        (D.cinnerCompl vector vector)) := by
  dsimp only
  exact centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    (by decide) K 0
    (globalInwardMateUniformPoincare_completed_vacuum_form_gap
      coverage certificate K hK)
    vector horthogonal

/-- Every same-object completed matrix coefficient has geometric squared-power
decay at the inward-mate rate. -/
theorem globalInwardMateUniformPoincare_completed_power_autocorrelationSq_decay
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (certificate : GlobalInwardMateUniformPoincareCertificate coverage)
    (K : Nat) (hK : 1 ≤ K) (n : Nat)
    (vector : CentralPhysicalGNSCompletion
      anchorCoupling (by decide) K 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      anchorCoupling (by decide) K 0 vector) :
    let rate := certificate.rate
    let D := (centralPhysicalSmulGNS
      anchorCoupling (by decide) K 0).toGNSData
    let propagated := centralPhysicalCompletedMarkovPower
      anchorCoupling (by decide) K 0 n vector
    CReal.RCle
      (CReal.RCmul
        (D.cinnerCompl propagated vector)
        (D.cinnerCompl propagated vector))
      (CReal.RCmul
        (CReal.RCscale ((rate * rate) ^ n)
          (D.cinnerCompl vector vector))
        (D.cinnerCompl vector vector)) := by
  dsimp only
  exact centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    (by decide) K 0
    (globalInwardMateUniformPoincare_completed_vacuum_form_gap
      coverage certificate K hK)
    n vector vector horthogonal

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier.globalInwardMateUniformPoincare_finiteQuadraticGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier.globalInwardMateUniformPoincare_completed_vacuum_form_gap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier.globalInwardMateUniformPoincare_completed_operator_norm_gap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSCompletedCarrier.globalInwardMateUniformPoincare_completed_power_autocorrelationSq_decay
