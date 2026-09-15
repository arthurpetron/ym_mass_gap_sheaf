/-
# Actual finite heat products in the ORIGINAL plaquette-observable algebra

Each heat factor is a finite rational sum of its actual SU(2) character
generators, with explicit physical lower-face membership. Products over
the original lower collar are expressions in the existing algebra.
Their independently defined lower and upper evaluations are pinned to the
original lower collar heat and its actual reflected upper heat product.

No replacement observable carrier or unproved evaluation relation is used.
The expression depends on the heat cutoff; it is not a fixed observable
when that cutoff varies, and no limiting or OS multiplier claim is made.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin

namespace YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def sumExpression {half : Nat} (f : Nat → PlaquetteExpression half) : List Nat → PlaquetteExpression half
  | [] => .smul 0 .unit
  | i :: ids => .add (f i) (sumExpression f ids)

private theorem sum_eval {half : Nat} (F : Nat → Nat → RatPoly) (f : Nat → PlaquetteExpression half) (g : Nat → RatPoly)
    (h : ∀ i, RatPolyCoeffEqv (evaluate F (f i)) (g i)) : ∀ ids,
    RatPolyCoeffEqv (evaluate F (sumExpression f ids)) (finitePolySum g ids)
  | [] => RatPolyCoeffEqv.zero_smul _
  | i :: ids => (h i).add (sum_eval F f g h ids)

def faceExpression (w : Q') (K : Nat) {half id : Nat} (hi : id ∈ centralLowerFaceIds half) : PlaquetteExpression half :=
  sumExpression (fun spin => .smul (coeffW w spin) (.character id hi spin)) (List.range (K+1))

theorem faceExpression_lower (w : Q') (K : Nat) {half id : Nat} (hi : id ∈ centralLowerFaceIds half) :
    RatPolyCoeffEqv (lower (faceExpression w K hi)) (faceHeatPolynomial w K (centralExtent half) id) := by
  rw [faceHeatPolynomial_eq_sum]
  exact sum_eval _ _ _ (fun _ => RatPolyCoeffEqv.refl _) _

theorem faceExpression_upper (w : Q') (K : Nat) {half id : Nat} (hi : id ∈ centralLowerFaceIds half) :
    RatPolyCoeffEqv (upper (faceExpression w K hi))
      (faceHeatPolynomial w K (centralExtent half) (slabFaceReflectId (centralExtent half) id)) := by
  rw [faceHeatPolynomial_eq_sum]
  exact sum_eval _ _ _ (fun _ => RatPolyCoeffEqv.refl _) _

def regionExpression (w : Q') (K half : Nat) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ centralLowerFaceIds half) → PlaquetteExpression half
  | [], _ => .unit
  | id :: ids, hi => .mul (faceExpression w K (hi id List.mem_cons_self))
      (regionExpression w K half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem regionExpression_lower (w : Q') (K half : Nat) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralLowerFaceIds half) →
    RatPolyCoeffEqv (lower (regionExpression w K half ids hi))
      (polynomialProduct (faceHeatPolynomial w K (centralExtent half)) ids)
  | [], _ => RatPolyCoeffEqv.refl _
  | id :: ids, hi => (faceExpression_lower w K (hi id List.mem_cons_self)).mul
      (regionExpression_lower w K half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem regionExpression_upper (w : Q') (K half : Nat) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralLowerFaceIds half) →
    RatPolyCoeffEqv (upper (regionExpression w K half ids hi))
      (polynomialProduct (fun id => faceHeatPolynomial w K (centralExtent half) (slabFaceReflectId (centralExtent half) id)) ids)
  | [], _ => RatPolyCoeffEqv.refl _
  | id :: ids, hi => (faceExpression_upper w K (hi id List.mem_cons_self)).mul
      (regionExpression_upper w K half ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def collarExpression (w : Q') (K half : Nat) : PlaquetteExpression half :=
  regionExpression w K half (lowerCollar half) (fun _ hi => collar_mem hi)

theorem collarExpression_lower (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (lower (collarExpression w K half)) (collarHeat w K half) :=
  regionExpression_lower w K half _ _

/-- Literal reflected face evaluation, not an assumed reflection pin. -/
theorem collarExpression_upper (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (upper (collarExpression w K half)) (upperCollarHeat w K half) := by
  simpa only [upperCollarHeat, reflectedCollarIds, polynomialProduct, List.foldr_map] using
    (regionExpression_upper w K half (lowerCollar half) (fun _ hi => collar_mem hi))

end YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.sumExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.faceExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.faceExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.faceExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.regionExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.regionExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.regionExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.collarExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.collarExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression.collarExpression_upper
