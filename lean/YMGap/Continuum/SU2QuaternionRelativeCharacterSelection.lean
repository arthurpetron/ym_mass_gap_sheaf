/-
# All-spin selection for a relative two-link character

Specialize only the auxiliary coefficient variables of the already proved
four-word harmonic identity to unit quaternions. The two real link variables
remain symbolic. Every solid spin other than one has zero conditional pairing
with a head coordinate; spin one returns half the retained coordinate.

The final ordinary-character identity uses the TWO proved Haar radius units,
and retains an arbitrary polynomial boundary. It is not a truncation of the
interacting action or a statement that its extra plaquettes are independent.
-/

import YMGap.Continuum.SU2QuaternionTailEvaluation
import YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionHaarSparseEquality

namespace YMGap.Continuum.SU2QuaternionRelativeCharacterSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarSparseEquality
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

local infix:50 " ≈ " => Q'.eqv

def relativeScalar : RatPoly :=
  (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))).scalar

def relativeRadius : RatPoly := polyMul (quaternionRadiusPolynomial 0) (quaternionRadiusPolynomial 1)

def relativeCharacter (spin : Nat) : RatPoly := characterPolynomial relativeScalar spin

/-- Explicit coefficient specialization; no physical Haar link is fixed here. -/
def auxiliaryUnits (i : Nat) : Q' := if i % 4 = 0 then 1 else 0

def specializedScalar : RatPoly := evaluateTail 8 auxiliaryUnits (exposedFourWord false true false false).scalar

def specializedRadius : RatPoly := evaluateTail 8 auxiliaryUnits fourQuaternionRadiusProduct

/-- The harmless zero padding from specialization is kept in the exact
coefficient carrier, and removed only through proved Haar equalities. -/
def relativeSolid (spin : Nat) : RatPoly := solidZonalCharacterPolynomial specializedScalar specializedRadius spin

theorem scalar_specialization (blocks : Nat) :
    HaarCarrierEqv blocks specializedScalar relativeScalar := by
  apply carrier_of_canon_check
  decide +kernel

theorem radius_specialization (blocks : Nat) :
    HaarCarrierEqv blocks specializedRadius relativeRadius := by
  apply carrier_of_canon_check
  decide +kernel

private theorem scalar_compact : RatPolyCoeffEqv specializedScalar
    (polyMul relativeScalar [(List.replicate 8 0, 1)]) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem solid_specialization : ∀ spin,
    RatPolyCoeffEqv (evaluateTail 8 auxiliaryUnits (exposedSolidZonalCharacter false true false false spin))
      (relativeSolid spin)
  | 0 => evaluate_one 8 auxiliaryUnits
  | 1 => evaluate_smul 8 auxiliaryUnits 2 _
  | spin+2 => by
    change RatPolyCoeffEqv (evaluateTail 8 auxiliaryUnits (polyAdd
      (polyMul (polySmul 2 (exposedFourWord false true false false).scalar)
        (exposedSolidZonalCharacter false true false false (spin+1)))
      (polySmul (-1) (polyMul fourQuaternionRadiusProduct (exposedSolidZonalCharacter false true false false spin))))) _
    rw [evaluate_add]
    apply RatPolyCoeffEqv.add
    · exact (evaluate_mul 8 auxiliaryUnits _ _).trans
        ((evaluate_smul 8 auxiliaryUnits 2 _).mul (solid_specialization (spin+1)))
    · exact (evaluate_smul 8 auxiliaryUnits (-1) _).trans
        (((evaluate_mul 8 auxiliaryUnits _ _).trans ((RatPolyCoeffEqv.refl specializedRadius).mul (solid_specialization spin))).smul (-1))

private theorem coordinate_specialization (i : Fin 4) :
    RatPolyCoeffEqv (evaluateTail 8 auxiliaryUnits (polyVar i.val)) (polyVar i.val) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  have h : ∀ j : Fin 4, RatPolyTermwiseEqv
      (canonRat (evaluateTail 8 auxiliaryUnits (polyVar j.val))) (canonRat (polyVar j.val)) := by decide +kernel
  exact h i

private theorem coordinate_degree (i : Fin 4) : headDegreeBound (polyVar i.val) = 1 := by
  have h : ∀ j : Fin 4, headDegreeBound (polyVar j.val) = 1 := by decide +kernel
  exact h i

/-- All higher spins vanish BEFORE any retained coordinate is integrated. -/
theorem high_spin_coordinate_zero (spin : Nat) (hs : 1 < spin) (i : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid spin) (polyVar i.val))) polyZero := by
  have hz := exposedSolid_partialHaar_zero false true false false spin (polyVar i.val)
    (by rw [coordinate_degree]; exact hs)
  have hp := (evaluate_mul 8 auxiliaryUnits _ _).trans
    ((solid_specialization spin).mul (coordinate_specialization i))
  exact (partialHaarHead_congr hp).symm.trans (partialHaarHead_evaluate_zero 4 auxiliaryUnits hz)

theorem spin_zero_coordinate_zero (i : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid 0) (polyVar i.val))) polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  have h : ∀ j : Fin 4, RatPolyTermwiseEqv
      (canonRat (partialHaarHead (polyMul (relativeSolid 0) (polyVar j.val)))) (canonRat polyZero) := by decide +kernel
  exact h i

theorem fundamental_coordinate (i : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid 1) (polyVar i.val)))
      (polySmul HalfPow.half [(List.ofFn (fun j : Fin 4 => if j = i then 1 else 0), 1)]) := by
  apply RatPolyCoeffEqv.trans (partialHaarHead_congr ((scalar_compact.smul 2).mul_right (polyVar i.val)))
  apply RatPolyCoeffEqv.of_canon_termwise
  have h : ∀ j : Fin 4, RatPolyTermwiseEqv
      (canonRat (partialHaarHead (polyMul (polySmul 2 (polyMul relativeScalar [(List.replicate 8 0, 1)])) (polyVar j.val))))
      (canonRat (polySmul HalfPow.half [(List.ofFn (fun k : Fin 4 => if k = j then 1 else 0), 1)])) := by decide +kernel
  exact h i

theorem solid_coordinate_selection (spin : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (relativeSolid spin) (polyVar i.val)))
      (if spin = 1 then polySmul HalfPow.half [(List.ofFn (fun j : Fin 4 => if j = i then 1 else 0), 1)] else polyZero) := by
  cases spin with
  | zero => exact spin_zero_coordinate_zero i
  | succ spin =>
    cases spin with
    | zero => exact fundamental_coordinate i
    | succ spin => exact high_spin_coordinate_zero (spin+2) (by omega) i

theorem relativeRadius_unit (blocks : Nat) (hb : 1 < blocks) :
    QuaternionHaarCarrierEqv blocks relativeRadius polyOne := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc blocks _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_mul_radius blocks 1 hb _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_mul_radius blocks 0 (by omega) _)
        (Q'.eqv_symm (quaternionHaar_polyMul_one_right blocks insertion))))

theorem solid_character_pin (blocks : Nat) (hb : 1 < blocks) (spin : Nat) :
    QuaternionHaarCarrierEqv blocks (relativeSolid spin) (relativeCharacter spin) := by
  have hr := (radius_specialization blocks).trans (relativeRadius_unit blocks hb)
  let rec hc : ∀ s, HaarCarrierEqv blocks
      (characterPolynomial specializedScalar s) (relativeCharacter s)
    | 0 => .refl _ _
    | 1 => QuaternionHaarCarrierEqv.smul 2 (scalar_specialization blocks)
    | s+2 => QuaternionHaarCarrierEqv.add
        (HaarCarrierEqv.mul (QuaternionHaarCarrierEqv.smul 2 (scalar_specialization blocks)) (hc (s+1)))
        (QuaternionHaarCarrierEqv.smul (-1) (hc s))
  exact (solidZonalCharacterPolynomial_eq_character_of_radius_eq_one _ _ hr spin).trans (hc spin)

private theorem lifted_independent (boundary : RatPoly) : HeadQuaternionIndependent (liftHead boundary) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  rfl

/-- Actual ordinary SU(2) characters, with an arbitrary polynomial tail.
The right-hand coordinate is V_i: head integration has shifted V to block zero. -/
theorem character_coordinate_boundary (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (spin : Nat) (i : Fin 4) (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeCharacter spin) (polyVar i.val)) (liftHead boundary)) ≈
      (if spin = 1 then HalfPow.half * quaternionHaar tailBlocks (polyMul (polyVar i.val) boundary) else 0) := by
  have hc : quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeCharacter spin) (polyVar i.val)) (liftHead boundary)) ≈
      quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeSolid spin) (polyVar i.val)) (liftHead boundary)) := by
    apply haar_of_carrier
    exact ((solid_character_pin (tailBlocks+1) (by omega) spin).symm.mul_right (polyVar i.val)).mul_right (liftHead boundary)
  have hf := quaternionHaar_polyMul_headIndependent tailBlocks
    (polyMul (relativeSolid spin) (polyVar i.val)) (liftHead boundary) (lifted_independent boundary)
  rw [drop_liftHead] at hf
  have hs := haar_of_coeff ((solid_coordinate_selection spin i).mul_right boundary) (blocks := tailBlocks)
  refine Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _ hs ?_))
  split
  · have hp : HaarCarrierEqv tailBlocks
        [(List.ofFn (fun j : Fin 4 => if j = i then 1 else 0), 1)] (polyVar i.val) := by
      apply carrier_of_canon_check
      have h : ∀ k : Fin 4, quaternionPrefixPolynomialCheck 0
          (canonRat [(List.ofFn (fun j : Fin 4 => if j = k then 1 else 0), 1)])
          (canonRat (polyVar k.val)) = true := by decide +kernel
      exact h i
    exact Q'.eqv_trans _ _ _ (haar_of_carrier (HaarCarrierEqv.mul_right boundary (QuaternionHaarCarrierEqv.smul HalfPow.half hp)))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
        (quaternionHaar_polySmul _ _ _))
  · exact Q'.eqv_refl _

end YMGap.Continuum.SU2QuaternionRelativeCharacterSelection

#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.relativeScalar
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.relativeRadius
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.relativeSolid
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.relativeCharacter
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.auxiliaryUnits
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.specializedScalar
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.specializedRadius
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.scalar_specialization
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.radius_specialization
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.solid_specialization
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.high_spin_coordinate_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.spin_zero_coordinate_zero
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.fundamental_coordinate
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.solid_coordinate_selection
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.relativeRadius_unit
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.solid_character_pin
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterSelection.character_coordinate_boundary
