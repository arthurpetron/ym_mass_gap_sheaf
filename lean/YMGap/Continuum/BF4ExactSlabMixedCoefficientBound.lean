/-
# Small-factor estimates for the ORIGINAL mixed-action boundary coefficient

The determinant uses the original Haar moments with a full selected action
in one copy and the filtered interior action in the other. Its exact Mobius
coefficient is pinned to the selective two-slot recursion, not to the older
diagonal connected coefficient. Interior faces cost kappa(w)=2*delta+delta^2;
exterior faces cost delta(w)=128*w^3. The computed bound names w and is
independent of the representation cutoff K. No volume summability, physical
decay or continuum gap is asserted.
-/

import YMGap.Continuum.PolynomialBiadditiveSelectiveMobius
import YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
import YMGap.Continuum.BF4ExactSlabMixedAction

namespace YMGap.Continuum.BF4ExactSlabMixedCoefficientBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.PolynomialBiadditive
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.PolynomialBiadditiveSelectiveMobius
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def mixedHaarForm (blocks : Nat) (p : RatPoly) : Biadditive :=
  (haarProduct blocks p polyOne).add (haarProduct blocks polyOne p).neg

theorem mixedHaarForm_pin (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (ids : List Nat) :
    (mixedHaarForm (boundaryCompleteSlabLinks extent).length p).value
      (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (faceHeatPolynomial w K extent) (inside keep ids)) ≈
        mixedNumerator w K extent keep p ids :=
  Q'.add_eqv_congr'
    (qmul (Q'.eqv_refl _) (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
    (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (qmul (haar_of_coeff (RatPolyCoeffEqv.one_mul _)) (Q'.eqv_refl _)) (Q'.mul_comm_eqv _ _)))

theorem mixedHaarForm_bound {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) :
    IntervalBound (mixedHaarForm blocks p) blocks (c+c) :=
  bound_change (Q'.add_eqv_congr' (Q'.mul_one_eqv c) (Q'.one_mul_eqv c))
    (bound_add (haarProduct_bound P (Interval.one blocks)) (bound_neg (haarProduct_bound (Interval.one blocks) P)))

/-- Data-level product, retaining the different interior and exterior costs. -/
def mixedHeatWeight (w : Q') (keep : Nat → Bool) (ids : List Nat) : Q' :=
  rateProduct (heatRemainderBound w) keep ids

theorem mixedHeatWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (keep : Nat → Bool) (ids : List Nat) :
    (0 : Q') ≤ mixedHeatWeight w keep ids :=
  rateProduct_nonnegative (heatRemainderBound_nonnegative hw) keep ids

theorem mixedHeatWeight_le_pairedPow {w : Q'} (hw : (0 : Q') ≤ w) (keep : Nat → Bool) (ids : List Nat) :
    mixedHeatWeight w keep ids ≤ (pairedHeatRate w)^ids.length :=
  rateProduct_le_pairedPow (heatRemainderBound_nonnegative hw) keep ids

theorem mixedCoefficient_selective_pin (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (ids : List Nat) :
    mixedCoefficient w K extent keep p ids ≈
      selectiveCoefficient (mixedHaarForm (boundaryCompleteSlabLinks extent).length p)
        (fun id => faceHeatTail w extent id 1 K) keep ids :=
  Q'.eqv_trans _ _ _ (coefficient_congr _ _ ids (fun ys _ => Q'.eqv_symm (mixedHaarForm_pin w K extent keep p ys)))
    (selectiveCoefficient_pin _ (faceHeatPolynomial w K extent) (fun id => faceHeatTail w extent id 1 K)
      keep (fun id => faceHeat_eq_one_add w extent id K) ids)

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
include hw0 hw1 hsmall

theorem mixedCoefficient_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (mixedCoefficient w K extent keep p ids) ≤ (c+c)*mixedHeatWeight w keep ids :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (mixedCoefficient_selective_pin w K extent keep p ids)))
    (selectiveCoefficient_bound _ (boundaryCompleteSlabLinks extent).length (c+c) (heatRemainderBound w)
      (mixedHaarForm_bound P) (fun id => faceHeatTail w extent id 1 K) keep ids
      (fun id hid => faceRemainderInterval hw0 hw1 hsmall extent id (hi id hid) K))

/-- Coarser cardinality estimate. The heat guard alone does not assert kappa<1. -/
theorem mixedCoefficient_geometric_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (mixedCoefficient w K extent keep p ids) ≤ (c+c)*(pairedHeatRate w)^ids.length :=
  Q'.le_trans' _ _ _ (mixedCoefficient_bound hw0 hw1 hsmall K extent keep p c P ids hi)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (mixedHeatWeight_le_pairedPow hw0 keep ids)
      (Q'.zero_le_add _ _ P.nonnegative P.nonnegative))

end SmallNome
end YMGap.Continuum.BF4ExactSlabMixedCoefficientBound

#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHaarForm
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHaarForm_pin
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHaarForm_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHeatWeight
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHeatWeight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedHeatWeight_le_pairedPow
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedCoefficient_selective_pin
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedCoefficient_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedCoefficientBound.mixedCoefficient_geometric_bound
