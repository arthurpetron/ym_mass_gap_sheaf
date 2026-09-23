/-
# Whole original product heat: block-local signed curvature

Costs add over the actual selected factors. Each factor uses only directions
at its upper endpoint, and retains every local mixed term. Repeated generator
coefficients remain inside the local l1 square; repeated heat factors are
counted with their actual multiplicity. There is no global direction-count
prefactor or replacement kernel.
-/

import YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature
import YMGap.Continuum.SU2QuaternionSignedAngularLocality

namespace YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionSignedAngularAlgebra
open YMGap.Continuum.SU2QuaternionSignedAngularLocality
open YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

theorem coefficientL1_upperTerms {n : Nat} : ∀ terms : List (AngularTerm n),
    coefficientL1 (upperTerms terms) = coefficientL1 terms
  | [] => rfl
  | term::terms => congrArg (fun c => Q'.abs term.coefficient+c)
      (coefficientL1_upperTerms terms)

def localCoefficientL1 {n : Nat} (terms : List (AngularTerm n)) (selected : Nat) : Q' :=
  coefficientL1 (terms.filter (fun term => decide (term.block.val = selected)))

def localCurvatureCost {n : Nat} (terms : List (AngularTerm n)) (C : Q') (selected : Nat) : Q' :=
  localCoefficientL1 terms selected * (localCoefficientL1 terms selected * C)

def productCurvatureCost {n : Nat} (terms : List (AngularTerm n)) (C : Q') : List Nat → Q'
  | [] => 0
  | i::ids => localCurvatureCost terms C i + productCurvatureCost terms C ids

/-- Localize BOTH derivatives before summing signed mixed heat entries. -/
def heatAt_localSignedCurvature {n : Nat} (selected : Fin n)
    (terms : List (AngularTerm n)) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) :
    let h := heatAt selected.val (n+selected.val) w K
    Certificate (n+n)
      (polyAdd (polyMul (cap (localCurvatureCost terms (logCurvatureCap w hw0 hw1) selected.val))
        (polyMul h h)) (signedNumerator h (upperTerms terms) (upperTerms terms))) := by
  let h := heatAt selected.val (n+selected.val) w K
  let localized := upperTerms (localTerms selected terms)
  have hleft : selected.val < n+n := by have := selected.isLt; omega
  have hright : n+selected.val < n+n := by have := selected.isLt; omega
  let B := signedHeatCurvature hleft hright hw0 hw1 K hK localized localized
  have first := upperDirection_localize selected terms h (heatAt_upperLocalAway n selected w K)
  have second := heatAt_upperDirection_second_localize n selected terms w K
  have localNumerator : RatPolyCoeffEqv (signedNumerator h (upperTerms terms) (upperTerms terms))
      (signedNumerator h localized localized) :=
    (second.mul_left h).add (RatPolyCoeffEqv.neg (first.mul first))
  have BL := B.lower
  dsimp only [localized] at BL
  rw [coefficientL1_upperTerms] at BL
  exact Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add localNumerator) BL

private theorem direction_zero {n : Nat} : ∀ terms : List (AngularTerm n),
    RatPolyCoeffEqv (signedAngularDirection terms polyZero) polyZero
  | [] => .refl _
  | term::terms =>
    ((RatPolyCoeffEqv.smul_zero term.coefficient).add (direction_zero terms)).trans (.zero_add _)

private theorem direction_one {n : Nat} : ∀ terms : List (AngularTerm n),
    RatPolyCoeffEqv (signedAngularDirection terms polyOne) polyZero
  | [] => .refl _
  | term::terms =>
    ((((angularDerivative_one _ _).smul term.coefficient).trans
      (RatPolyCoeffEqv.smul_zero term.coefficient)).add (direction_one terms)).trans (.zero_add _)

private def unitCurvature {n : Nat} (terms : List (AngularTerm n)) :
    Certificate n (polyAdd (polyMul (cap 0) (polyMul polyOne polyOne))
      (signedNumerator polyOne terms terms)) := by
  have first := direction_one terms
  have second := (direction_congr terms first).trans (direction_zero terms)
  have num : RatPolyCoeffEqv (signedNumerator polyOne terms terms) polyZero :=
    (((second.mul_left polyOne).trans (RatPolyCoeffEqv.mul_zero_right polyOne)).add
      (RatPolyCoeffEqv.neg ((first.mul first).trans (RatPolyCoeffEqv.mul_zero_left polyZero)))).trans
      (.zero_add _)
  exact Certificate.ofCoeff
    (((cap_mul_left 0 _).trans (RatPolyCoeffEqv.zero_smul _)).add num |>.trans (.zero_add _))
    (Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant n 0 (Q'.le_refl' _)))

/-- The ACTUAL whole selected kernel has additive block-local curvature cost.
No distinctness is assumed: duplicate factors pay their literal multiplicity. -/
def productHeat_signedCurvature (n : Nat) (terms : List (AngularTerm n))
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < n) →
    let W := productHeat n w K ids
    Certificate (n+n)
      (polyAdd (polyMul (cap (productCurvatureCost terms (logCurvatureCap w hw0 hw1) ids))
        (polyMul W W)) (signedNumerator W (upperTerms terms) (upperTerms terms)))
  | [], _ => unitCurvature (upperTerms terms)
  | i::ids, hi => by
    have hii : i < n := hi i List.mem_cons_self
    have htail : ∀ j, j ∈ ids → j < n := fun j hj => hi j (List.mem_cons_of_mem i hj)
    exact signedAngular_productLogCurvatureLower (upperTerms terms)
      (heatAt i (n+i) w K) (productHeat n w K ids)
      (localCurvatureCost terms (logCurvatureCap w hw0 hw1) i)
      (productCurvatureCost terms (logCurvatureCap w hw0 hw1) ids)
      (heat_supported (by omega) (by omega) w K)
      (productHeat_supported n w K ids htail)
      (heatAt_localSignedCurvature ⟨i,hii⟩ terms hw0 hw1 K hK)
      (productHeat_signedCurvature n terms hw0 hw1 K hK ids htail)

end YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature.coefficientL1_upperTerms
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature.heatAt_localSignedCurvature
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature.productHeat_signedCurvature
