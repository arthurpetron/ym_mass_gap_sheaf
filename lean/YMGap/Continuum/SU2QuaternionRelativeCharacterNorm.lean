/-
# All-spin norm of the original two-link relative character

The existing harmonic reproducing identity is applied to the solid relative
character with BOTH physical quaternion links retained. After diagonal
substitution, its scalar and radius arguments are recomputed as the retained
radius and its square. Only then is the actual one-link Haar sphere relation
used. No arbitrary Haar equality is transported through substitution.

The result supplies the nonzero norm needed for uniqueness of every realized
SU(2) Casimir reading. It is an exact polynomial Haar theorem, not a compact
group realization, interacting norm identity, or continuum gap statement.
-/

import YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
import YMGap.Continuum.SU2QuaternionHaarSparseEquality
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.SU2QuaternionRelativeCharacterNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarSparseEquality
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionTailEvaluationDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private def raw (s : Nat) : RatPoly :=
  evaluateTail 8 auxiliaryUnits (exposedSolidZonalCharacter false true false false s)

private theorem raw_degree (s : Nat) : HasQuaternionBlockDegree 0 s (raw s) :=
  evaluate_headDegree 8 auxiliaryUnits (by decide)
    (exposedSolidZonalCharacter_blockDegree false true false false 0 (by decide) s)

private theorem raw_harmonic (s : Nat) :
    RatPolyCoeffEqv (headLaplacian (raw s)) polyZero :=
  (evaluate_headLaplacian 8 auxiliaryUnits (by decide) _).trans
    (evaluate_congr 8 auxiliaryUnits
      (laplacian_exposedSolidZonalCharacter_zero false true false false s))

private theorem raw_character (s : Nat) :
    QuaternionHaarCarrierEqv 2 (raw s) (relativeCharacter s) :=
  (RatPolyCoeffEqv.haarCarrier (solid_specialization s)).trans
    (solid_character_pin 2 (by decide) s)

private theorem substitute_one :
    RatPolyCoeffEqv (substituteRetained polyOne) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substitute_solid (scalar radius : RatPoly) : ∀ s,
    RatPolyCoeffEqv
      (substituteRetained (solidZonalCharacterPolynomial scalar radius s))
      (solidZonalCharacterPolynomial (substituteRetained scalar)
        (substituteRetained radius) s)
  | 0 => substitute_one
  | 1 => substituteRetained_smul 2 scalar
  | s+2 => (substituteRetained_add _ _).trans
      (((substituteRetained_mul _ _).trans
        ((substituteRetained_smul 2 scalar).mul (substitute_solid scalar radius (s+1)))).add
        ((substituteRetained_smul (-1) _).trans
          (((substituteRetained_mul _ _).trans
            ((RatPolyCoeffEqv.refl _).mul (substitute_solid scalar radius s))).smul (-1))))

-- These are fixed polynomial calculations AFTER substitution. In particular,
-- scalar_specialization/radius_specialization are not substituted as Haar equalities.
private theorem diagonal_scalar :
    QuaternionHaarCarrierEqv 1 (substituteRetained specializedScalar) polyOne := by
  have h : QuaternionHaarCarrierEqv 1 (substituteRetained specializedScalar)
      (quaternionRadiusPolynomial 0) := by
    apply carrier_of_canon_check
    decide +kernel
  exact h.trans (quaternionRadiusPolynomial_carrier_one (by decide : 0 < 1))

private theorem diagonal_radius :
    QuaternionHaarCarrierEqv 1 (substituteRetained specializedRadius) polyOne := by
  have h : QuaternionHaarCarrierEqv 1 (substituteRetained specializedRadius)
      (polyMul (quaternionRadiusPolynomial 0) (quaternionRadiusPolynomial 0)) := by
    apply carrier_of_canon_check
    decide +kernel
  have hr : QuaternionHaarCarrierEqv 1 (quaternionRadiusPolynomial 0) polyOne :=
    quaternionRadiusPolynomial_carrier_one (by decide : 0 < 1)
  exact h.trans ((hr.mul hr).trans (quaternionHaarCarrierEqv_one_mul 1 polyOne))

private theorem character_congr {p q : RatPoly}
    (h : QuaternionHaarCarrierEqv 1 p q) : ∀ s,
    QuaternionHaarCarrierEqv 1 (characterPolynomial p s) (characterPolynomial q s)
  | 0 => QuaternionHaarCarrierEqv.refl 1 polyOne
  | 1 => h.smul 2
  | s+2 => ((h.smul 2).mul (character_congr h (s+1))).add
      ((character_congr h s).smul (-1))

private theorem dimension_recurrence (s : Nat) :
    2*Q'.ofNat (s+2) + (-1)*Q'.ofNat (s+1) ≈ Q'.ofNat (s+3) := by
  change ((2*((s+2 : Nat) : Int))*1 + ((-1)*((s+1 : Nat) : Int))*1)*1 =
    ((s+3 : Nat) : Int)*1
  simp only [Int.mul_one, Int.natCast_add]
  omega

private theorem character_one : ∀ s,
    RatPolyCoeffEqv (characterPolynomial polyOne s)
      (polySmul (Q'.ofNat (s+1)) polyOne)
  | 0 => (RatPolyCoeffEqv.one_smul _).symm
  | 1 => .refl _
  | s+2 => by
      have ha := ((RatPolyCoeffEqv.refl (polySmul 2 polyOne)).mul (character_one (s+1))).trans
        ((RatPolyCoeffEqv.polyMul_smul_left 2 polyOne _).trans
          (((RatPolyCoeffEqv.one_mul _).smul 2).trans (RatPolyCoeffEqv.smul_assoc _ _ _)))
      have hb := ((character_one s).smul (-1)).trans (RatPolyCoeffEqv.smul_assoc _ _ _)
      exact (ha.add hb).trans
        ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
          (RatPolyCoeffEqv.smul_coefficient (dimension_recurrence s) _))

private theorem diagonal_value (s : Nat) :
    QuaternionHaarCarrierEqv 1 (substituteRetained (raw s))
      (polySmul (Q'.ofNat (s+1)) polyOne) :=
  (RatPolyCoeffEqv.haarCarrier (substituteRetained_congr (solid_specialization s))).trans
    ((RatPolyCoeffEqv.haarCarrier (substitute_solid _ _ s)).trans
      ((solidZonalCharacterPolynomial_eq_character_of_radius_eq_one _ _ diagonal_radius s).trans
        ((character_congr diagonal_scalar s).trans
          (RatPolyCoeffEqv.haarCarrier (character_one s)))))

/-- Every label has norm one in the SAME original two-quaternion Haar
functional used by the realized relative-character Casimir reading. -/
theorem relativeCharacter_square_norm (s : Nat) :
    quaternionHaar 2 (polyMul (relativeCharacter s) (relativeCharacter s)) ≈ 1 := by
  let c := Q'.ofNat (s+1)
  let p := polyMul (relativeCharacter s) (raw s)
  have hf := quaternionHaar_partialHaarHead 1 p
  have hr := haar_of_coeff (blocks := 1)
    (character_harmonic_reproduction s (raw s) (raw_degree s) (raw_harmonic s))
  have hscaled : c * quaternionHaar 2 p ≈ quaternionHaar 1 (substituteRetained (raw s)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hf))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul 1 c _)) hr)
  have hvalue : quaternionHaar 1 (substituteRetained (raw s)) ≈ c :=
    Q'.eqv_trans _ _ _ (haar_of_carrier (diagonal_value s))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 1 c polyOne)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _
          (by decide +kernel : quaternionHaar 1 polyOne ≈ 1)) (Q'.mul_one_eqv c)))
  have hnorm := haar_of_carrier ((raw_character s).mul_left (relativeCharacter s))
  apply Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos s)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hnorm))
    (Q'.eqv_trans _ _ _ hscaled
      (Q'.eqv_trans _ _ _ hvalue (Q'.eqv_symm (Q'.mul_one_eqv c))))

end YMGap.Continuum.SU2QuaternionRelativeCharacterNorm

#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterNorm.relativeCharacter_square_norm
