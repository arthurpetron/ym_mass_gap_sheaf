/-
Machine-checked obstruction to pointwise positivity on the square-root proof
window.

The finite repartition checkpoint is frozen.  Its right endpoint is useful
for cumulative payment, but it cannot be discharged by summing pointwise
nonnegative cells: the endpoint cell is already strictly negative at the
threshold scale.  This file banks that obstruction and the corresponding
failure of the first-order Bernoulli square carrier.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowSign

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- The exact right endpoint of the proof window at the threshold scale. -/
theorem thetaWindowCenter_k38 : thetaWindowCenter 38 = 9 := by
  unfold thetaWindowCenter thetaWindowLength
    ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux
  decide

theorem thetaWindowLeft_k38 : thetaWindowLeft 38 = 4 := by
  rw [thetaWindowLeft, thetaWindowCenter_k38]

/-- The proof-window endpoint is a genuinely negative core cell. -/
theorem thetaCoreIncrement_k38_center_neg :
    thetaCoreIncrement 38 (thetaWindowCenter 38) < (0 : Q') := by
  rw [thetaWindowCenter_k38]
  unfold thetaCoreIncrement sevenDirichletProfile thetaDirichletCell
    thetaRootTerm integerThetaTerm harmW harmU
    ReciprocalBernoulliUpper.oneSub unit qpow
  decide

/-- Consequently, pointwise nonnegativity on the proof window is false. -/
theorem thetaProofWindow_pointwise_nonnegative_fails_k38 :
    ¬ (∀ n : Nat,
      thetaWindowLeft 38 ≤ n →
      n ≤ thetaWindowCenter 38 →
      (0 : Q') ≤ thetaCoreIncrement 38 n) := by
  intro h
  have hnonneg := h 9 (by rw [thetaWindowLeft_k38]; decide)
    (by rw [thetaWindowCenter_k38]; decide)
  have hneg : thetaCoreIncrement 38 9 < (0 : Q') := by
    simpa [thetaWindowCenter_k38] using thetaCoreIncrement_k38_center_neg
  exact Int.lt_irrefl _ (Q'.lt_of_le_of_lt hnonneg hneg)

/-- First-order lower Bernoulli produces this upper carrier for a
nonnegative root slope. -/
def thetaFirstOrderRightCarrier (k n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) *
      ((1 : Q') + -(Q'.ofNat (2 * n + 1) * harmU k)))

/-- At the same endpoint the squared first-order carrier already exceeds the
available Dirichlet profile. -/
theorem thetaFirstOrderRightCarrier_k38_center_fails :
    ¬ (Q'.ofNat 4 *
        (thetaFirstOrderRightCarrier 38 (thetaWindowCenter 38) *
          thetaFirstOrderRightCarrier 38 (thetaWindowCenter 38)) ≤
      sevenDirichletProfile 38 *
        Q'.ofNat (thetaWindowCenter 38 * thetaWindowCenter 38)) := by
  rw [thetaWindowCenter_k38]
  unfold thetaFirstOrderRightCarrier sevenDirichletProfile harmU unit
  decide

#print axioms thetaWindowCenter_k38
#print axioms thetaWindowLeft_k38
#print axioms thetaCoreIncrement_k38_center_neg
#print axioms thetaProofWindow_pointwise_nonnegative_fails_k38
#print axioms thetaFirstOrderRightCarrier
#print axioms thetaFirstOrderRightCarrier_k38_center_fails

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowSign
