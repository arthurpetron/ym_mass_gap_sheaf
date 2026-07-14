/-
Cleared finite-flux normal form for the remaining lower-six payment.

The imported file identifies the exact physical target with an endpoint
augmentation, a complete ordinary-mode Taylor sum, and the signed prefix
correction.  Here the ordinary sum is passed through the finite-D Hermite
telescope.  Thus the only remaining analytic statement is a concrete lower
bound for two flux endpoints, a positive mass sum, the summed finite-D
remainder, and the cleared prefix correction.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem flux_envelope_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "flux_envelope_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               flux_envelope_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The positive integer clearing scale used by the finite Hermite flux. -/
def lowerSixQuadraticTaylorClearingScale (k : Nat) : Q' :=
  Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4

theorem lowerSixQuadraticTaylorClearingScale_pos (k : Nat) :
    (0 : Q') < lowerSixQuadraticTaylorClearingScale k := by
  let D := Q'.ofNat (k + 2)
  have hD : (0 : Q') < D := by
    dsimp only [D]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Q'.ofNat_succ_pos (k + 1))
  have h1 : (0 : Q') < (1 : Q') := by decide
  have h2 : (0 : Q') < (1 : Q') * D := Q'.mul_pos h1 hD
  have h3 : (0 : Q') < ((1 : Q') * D) * D := Q'.mul_pos h2 hD
  have h4 : (0 : Q') < (((1 : Q') * D) * D) * D := Q'.mul_pos h3 hD
  have h5 : (0 : Q') < ((((1 : Q') * D) * D) * D) * D :=
    Q'.mul_pos h4 hD
  unfold lowerSixQuadraticTaylorClearingScale RingNormaliser.qpow
  dsimp only [D] at h5
  exact Q'.mul_pos (by decide) h5

/-- The fully explicit cleared expression left by the exact finite Hermite
telescope. -/
def lowerSixQuadraticTaylorClearedFluxExpression (k : Nat) : Q' :=
  (lowerSixQuadraticTaylorClearingScale k *
        lowerSixQuadraticTaylorEndpointAugmentation k +
      (((lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1) +
            -lowerSixDiscreteHermiteFluxNumerator k 1) +
          finSum
            (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1))
            (growingAnchor k)) +
        finSum
          (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
          (growingAnchor k))) +
  lowerSixQuadraticTaylorClearingScale k *
    lowerSixQuadraticTaylorPrefixRemainder k

/-- Exact cleared normal form for the true physical target. -/
theorem lowerSixQuadraticTaylorTarget_cleared_finite_flux
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixQuadraticTaylorClearingScale k *
        lowerSixQuadraticTaylorTarget k ≈
      lowerSixQuadraticTaylorClearedFluxExpression k := by
  let C := lowerSixQuadraticTaylorClearingScale k
  let E := lowerSixQuadraticTaylorEndpointAugmentation k
  let S := finSum
    (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
    (growingAnchor k)
  let P := lowerSixQuadraticTaylorPrefixRemainder k
  let F := lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1) +
    -lowerSixDiscreteHermiteFluxNumerator k 1
  let M := finSum
    (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1))
    (growingAnchor k)
  let R := finSum
    (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
    (growingAnchor k)
  have ht := lowerSixQuadraticTaylorTarget_eqv_endpoint_add_finSum_add_remainder hk
  have hsum := lowerSixQuadraticTaylorWeightedFinSum_finite_flux
    k (growingAnchor k)
  have hscale : C * lowerSixQuadraticTaylorTarget k ≈
      C * ((E + S) + P) := by
    exact Q'.mul_eqv_congr_left C _ _ ht
  have hsum' : C * S ≈ (F + M) + R := by
    dsimp only [C, S, F, M, R, lowerSixQuadraticTaylorClearingScale]
    exact hsum
  unfold lowerSixQuadraticTaylorClearedFluxExpression
  dsimp only [C, E, S, P, F, M, R] at hscale hsum' ⊢
  refine Q'.eqv_trans _ _ _ hscale ?_
  refine Q'.eqv_trans _
    (C * (E + S) + C * P) _
    (Q'.mul_add_eqv C (E + S) P) ?_
  refine Q'.eqv_trans _
    ((C * E + C * S) + C * P) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv C E S)) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_left (C * E) _ _ hsum')

/-- Positivity of the explicit cleared expression is exactly sufficient for
the requested quadratic payment. -/
theorem lowerSixQuadraticPayment_of_clearedFluxExpression_nonnegative
    {k : Nat} (hk : 48 ≤ k)
    (h : (0 : Q') ≤ lowerSixQuadraticTaylorClearedFluxExpression k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  have hscaled : (0 : Q') ≤
      lowerSixQuadraticTaylorClearingScale k *
        lowerSixQuadraticTaylorTarget k :=
    Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (lowerSixQuadraticTaylorTarget_cleared_finite_flux hk)))
  have hzero : lowerSixQuadraticTaylorClearingScale k * (0 : Q') ≤
      lowerSixQuadraticTaylorClearingScale k *
        lowerSixQuadraticTaylorTarget k :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_zero_eqv (lowerSixQuadraticTaylorClearingScale k)))
      hscaled
  have htarget : (0 : Q') ≤ lowerSixQuadraticTaylorTarget k :=
    Q'.le_of_mul_le_mul_left hzero
      (lowerSixQuadraticTaylorClearingScale_pos k)
  exact quadratic_payment_of_taylorTarget_nonnegative htarget

#print axioms lowerSixQuadraticTaylorClearingScale_pos
#print axioms lowerSixQuadraticTaylorTarget_cleared_finite_flux
#print axioms lowerSixQuadraticPayment_of_clearedFluxExpression_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
