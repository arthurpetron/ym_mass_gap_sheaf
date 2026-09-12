/-
# Exposed-character selection on every sufficiently large Haar carrier

The canonical four-link character has zero product-Haar pairing against
every fixed multiplier of smaller head degree, for any number of blocks
at least four. The solid harmonic argument retains all tail coefficients;
the four radius-unit identities are proved on the same full carrier.

This removes the old 116-block specialization without changing that
consumer. The bound is an explicit polynomial degree, not a decay rate,
and the statement is not a physical spectral estimate.
-/

import YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
import YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection

namespace YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection

local infix:50 " ≈ " => Q'.eqv

/-- All four radii are integrated in the displayed full Haar carrier. -/
theorem exposedSolid_eq_character {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) :
    QuaternionHaarCarrierEqv blocks (exposedSolidZonalCharacter r0 r1 r2 r3 spin)
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) :=
  solidZonalCharacterPolynomial_eq_character_of_radius_eq_one _ _
    (fourQuaternionRadiusProductAt_eq_one blocks 0 1 2 3
      (by omega) (by omega) (by omega) hb) spin

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

/-- Exact original-character cancellation with every tail variable retained. -/
theorem exposedCharacter_haar_zero {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) (p : RatPoly)
    (hs : headDegreeBound p < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) p) ≈ 0 := by
  cases blocks with
  | zero => omega
  | succ tail =>
    let solid := exposedSolidZonalCharacter r0 r1 r2 r3 spin
    let ordinary := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin
    have hz : quaternionHaar tail (partialHaarHead (polyMul solid p)) ≈ 0 := by
      rw [haar_weighted]
      exact exposedSolid_partialHaar_zero r0 r1 r2 r3 spin p hs (quaternionHaarMono tail)
    have hc := exposedSolid_eq_character hb r0 r1 r2 r3 spin p
    exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm (tail + 1) ordinary p)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm (tail + 1) p solid)
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead tail _)) hz)))

/-- Unrestricted factors independent of the selected block do not enter
the explicit bound. No bound on their degrees in other blocks is assumed. -/
theorem exposedCharacter_independent_product_zero {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) (p q : RatPoly)
    (hq : HasQuaternionBlockDegree 0 0 q) (hs : headDegreeBound p < spin) :
    quaternionHaar blocks (polyMul
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) (polyMul p q)) ≈ 0 :=
  exposedCharacter_haar_zero hb r0 r1 r2 r3 spin _
    (Nat.lt_of_le_of_lt (headDegreeBound_mul_independent p q hq) hs)

end YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection

#print axioms YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection.exposedSolid_eq_character
#print axioms YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection.exposedCharacter_haar_zero
#print axioms YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection.exposedCharacter_independent_product_zero
