/-
# Actual regularized entropy of the ORIGINAL identity-normalized slab action

The weight is the full original heat product divided by H_K(1)^ids.length.
Every factor, including repetitions and shared link variables, is retained.
Its positive pointwise window and positive Haar mass are constructed from
the finiteCutoff floor, not supplied as new analytic inputs.

The entropy value uses the literal finite Haar integrals of entropyStage n W
with the computed uniform modulus. The logarithmic upper bound is centered
at its OWN partition Z=Haar(W), explicitly pinned to the original raw
partition divided by H_K(1)^ids.length. It does not replace W by W/Z.

This is a finite-carrier entropy-series limit and scalar logarithmic Jensen
bound. No volume-uniform entropy, concentration, H1, physical normalization,
Hamiltonian gap or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabOriginalFiniteEntropy
import YMGap.Continuum.QuaternionHaarRegularizedEntropy

namespace YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage)
open YMGap.Continuum.RegularizedLogBinaryReduction (binaryReduction)
open YMGap.Continuum.RebasedExpShiftSupportReduction (dyadicLogValue)

/-- The OWN Haar mass of the identity-normalized ORIGINAL action. -/
def originalPartition (w : Q') (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks extent).length
    (normalizedHeatProduct w hw0 K extent ids)

/-- Exact original partition pin; this is identity, not probability,
normalization. No late-cutoff hypothesis is needed for this algebraic pin. -/
theorem originalPartition_pin (w : Q') (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) :
    Q'.eqv (originalPartition w hw0 K extent ids)
      (normalizingFactor w hw0 K ids*
        heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K) :=
  normalizedHeatProductHaar_pin w hw0 K extent ids

/-- Strict positivity is paid by the actual finite product floor. -/
theorem originalPartition_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) :
    (0 : Q') < originalPartition w hw0 K extent ids :=
  Q'.pos_of_lt_of_le (normalizedFloor_positive hw0 hw1 K ids)
    (normalizedHeatProductHaar_bounds hw0 hw1 K extent ids hK).1

theorem originalPartition_le_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) :
    originalPartition w hw0 K extent ids ≤ (1 : Q') :=
  (normalizedHeatProductHaar_bounds hw0 hw1 K extent ids hK).2

private theorem original_weight_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1)
    (qs : Nat → UnitNorm) :
    (0 : Q') ≤ evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) :=
  Q'.le_trans' _ _ _ (Q'.le_of_lt (normalizedFloor_positive hw0 hw1 K ids))
    (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).1

/-- The actual generic entropy construction applied to the literal original
polynomial; no alternative density or integral is introduced. -/
def original_entropyValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) : CReal :=
  QuaternionHaarRegularizedEntropy.entropyValue
    (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids)
    (normalizedHeatProduct_supported w hw0 K extent ids)
    (original_weight_nonnegative hw0 hw1 K extent ids hK)
    (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).2)

/-- The computed modulus is retained as Type-valued regularity data. -/
def original_entropyRegularity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) :
    CReal.InnerRegularity (original_entropyValue hw0 hw1 K extent ids hK) :=
  QuaternionHaarRegularizedEntropy.entropyRegularity
    (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids)
    (normalizedHeatProduct_supported w hw0 K extent ids)
    (original_weight_nonnegative hw0 hw1 K extent ids hK)
    (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).2)

/-- Literal approximation-stream pin, with the original entropy cutoff n. -/
theorem original_entropyValue_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) (n : Nat) :
    (original_entropyValue hw0 hw1 K extent ids hK).approx n =
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (entropyStage n (normalizedHeatProduct w hw0 K extent ids)) := rfl

/-- Logarithmic upper bound with the OWN positive original partition. Both
the nome/cutoff floor and binary-log comparison rate are explicit. -/
theorem original_entropy_log_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : RegularizedLogBinaryIdentification.identificationRate epsilon ≤ n) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
        (entropyStage n (normalizedHeatProduct w hw0 K extent ids)) ≤
      (CReal.neg (CReal.mul (CReal.ofQ' (originalPartition w hw0 K extent ids))
        (dyadicLogValue (binaryReduction (originalPartition w hw0 K extent ids)
          (originalPartition_positive hw0 hw1 K extent ids hK)
          (originalPartition_le_one hw0 hw1 K extent ids hK))))).approx n+epsilon :=
  QuaternionHaarRegularizedEntropy.haar_entropy_log_approx
    (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids)
    (normalizedHeatProduct_supported w hw0 K extent ids)
    (original_weight_nonnegative hw0 hw1 K extent ids hK)
    (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).2)
    (originalPartition_positive hw0 hw1 K extent ids hK) epsilon he n hn

end YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy

#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.originalPartition
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.originalPartition_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.originalPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.originalPartition_le_one
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.original_entropyValue
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.original_entropyRegularity
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.original_entropyValue_approx
#print axioms YMGap.Continuum.BF4ExactSlabOriginalRegularizedEntropy.original_entropy_log_approx
