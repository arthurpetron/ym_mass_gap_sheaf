/-
# Small-nome bounds for the ACTUAL original connected Mobius coefficients

The existing connectedCoefficient is pinned to the constructed two-slot
Haar form and its exact three-term insertion recursion. It has the bound
2*c_p*c_q*kappa(w)^n, with kappa(w)=2*delta(w)+delta(w)^2 and
delta(w)=128*w^3, for every cutoff/extent under the explicit heat guard.

The general guard does NOT assert kappa<1. Strict smallness is checked at
the existing 1/1024 pilot. No normalized sum, distance decay or gap follows
from a per-coefficient bound alone.
-/

import YMGap.Continuum.QuaternionHaarBiadditive
import YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion

namespace YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def pairedHeatRate (w : Q') : Q' := pairedRate (heatRemainderBound w)

theorem pairedHeatRate_eq (w : Q') : pairedHeatRate w ≈
    (128*qpow w 3)+(128*qpow w 3)+(128*qpow w 3)*(128*qpow w 3) :=
  Q'.add_eqv_congr' (Q'.add_eqv_congr' (heatRemainderBound_eq w) (heatRemainderBound_eq w))
    (qmul (heatRemainderBound_eq w) (heatRemainderBound_eq w))

theorem pairedHeatRate_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) : (0 : Q') ≤ pairedHeatRate w :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (heatRemainderBound_nonnegative hw) (heatRemainderBound_nonnegative hw))
    (Q'.mul_nonneg _ _ (heatRemainderBound_nonnegative hw) (heatRemainderBound_nonnegative hw))

/-- Existing rational pilot only; the heat guard alone does not imply this. -/
theorem existingNome_rate : (0 : Q') < pairedHeatRate BF4ExactSlabPlaquetteSmallNomeCertificate.nome ∧
    pairedHeatRate BF4ExactSlabPlaquetteSmallNomeCertificate.nome < (1 : Q') := by decide

theorem connectedCoefficient_pair_pin (w : Q') (K extent : Nat) (p q : RatPoly) (ids : List Nat) :
    connectedCoefficient w K extent p q ids ≈
      pairedCoefficient (connected (boundaryCompleteSlabLinks extent).length p q)
        (fun id => faceHeatTail w extent id 1 K) ids :=
  Q'.eqv_trans _ _ _ (coefficient_congr _ _ ids (fun ys _ => Q'.eqv_symm
    (connected_diagonal (boundaryCompleteSlabLinks extent).length p q (polynomialProduct (faceHeatPolynomial w K extent) ys))))
    (pairedCoefficient_pin _ (faceHeatPolynomial w K extent) (fun id => faceHeatTail w extent id 1 K)
      (fun id => faceHeat_eq_one_add w extent id K) ids)

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
include hw0 hw1 hsmall

theorem connectedCoefficient_bound (K extent : Nat) (p q : RatPoly) (c d : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Q : Interval (boundaryCompleteSlabLinks extent).length q d) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedCoefficient w K extent p q ids) ≤ (c*d+c*d)*(pairedHeatRate w)^ids.length :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (connectedCoefficient_pair_pin w K extent p q ids)))
    (pairedCoefficient_bound _ (boundaryCompleteSlabLinks extent).length (c*d+c*d) (heatRemainderBound w)
      (connected_bound P Q) (fun id => faceHeatTail w extent id 1 K) ids
      (fun id hid => faceRemainderInterval hw0 hw1 hsmall extent id (hi id hid) K))

end SmallNome
end YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound

#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.pairedHeatRate
#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.pairedHeatRate_eq
#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.pairedHeatRate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.existingNome_rate
#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.connectedCoefficient_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound.connectedCoefficient_bound
