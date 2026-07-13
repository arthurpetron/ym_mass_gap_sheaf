/-
Exact combined two-tail payment on the first complete square-root band, and
its immediate transport to the harmonic moving-determinant spacing target.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicAllPrefixes

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBandPayment

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- Exact combined left/right-tail payment on every scale of the first
complete center band. -/
theorem thetaProof_window_payment_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    thetaLeftLoss k + thetaProofRightLoss k ≤
      thetaProofCentralReserve k := by
  have hk : k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨
      k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 := by
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold thetaLeftLoss thetaProofRightLoss thetaLeftTailSum
      thetaProofRightTailSum thetaProofCentralReserve thetaCoreIncrement
      thetaWindowLeft thetaWindowCenter thetaWindowLength sevenDirichletProfile
      thetaDirichletCell thetaRootTerm integerThetaTerm harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit
      ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux
      YMGap.Constructive.RationalTail.finSum qpow <;>
    decide

theorem sevenDirichletCoreGap_firstBand_nonnegative {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    (0 : Q') ≤ sevenDirichletCoreGap k :=
  sevenDirichletCoreGap_nonnegative_of_proof_window hk0
    (thetaProof_window_payment_firstBand hk0 hk1)

theorem sevenUnitResidualGap_firstBand_nonnegative {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    (0 : Q') ≤ sevenUnitResidualGap k :=
  sevenUnitResidualGap_nonnegative_of_core
    (sevenDirichletCoreGap_firstBand_nonnegative hk0 hk1)

theorem old_pascal_eight_budget_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k) :=
  old_pascal_eight_budget_of_seven_gap hk0
    (sevenUnitResidualGap_firstBand_nonnegative hk0 hk1)

/-- Earliest frozen upstream physical consumer of the combined payment. -/
theorem harmonicMass_shell_spacing_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k :=
  harmonicMass_shell_spacing_of_old_pascal_eight_budget hk0
    (old_pascal_eight_budget_firstBand hk0 hk1)

#print axioms thetaProof_window_payment_firstBand
#print axioms sevenDirichletCoreGap_firstBand_nonnegative
#print axioms sevenUnitResidualGap_firstBand_nonnegative
#print axioms old_pascal_eight_budget_firstBand
#print axioms harmonicMass_shell_spacing_firstBand

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBandPayment
