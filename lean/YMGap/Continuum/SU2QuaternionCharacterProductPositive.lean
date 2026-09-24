/-
# Positive quadratics for finite products of normalized relative characters

Each normalized relative character is a positive scalar multiple of one
representation-channel Gram kernel.  The existing character insertion theorem
therefore lets us adjoin such factors one at a time while preserving positivity
of the same endpoint quadratic.  Slots may repeat.

This is a finite kernel statement.  It does not assert a joint harmonic
decomposition or any interacting-transfer estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPositive

namespace YMGap.Continuum.SU2QuaternionCharacterProductPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The dimension-normalized character of the relative quaternion `left/right`. -/
def normalizedCharacterAt (left right degree : Nat) : RatPoly :=
  polySmul (Q'.ofNat (degree+1)) (characterPolynomial (scalarAt left right) degree)

/-- A finite product of normalized lower/upper character channels.  Each list
entry is `(lower slot, representation degree)`. -/
def characterProduct (blocks : Nat) (channels : List (Nat × Nat)) : RatPoly :=
  polynomialProduct
    (fun channel => normalizedCharacterAt channel.1 (blocks+channel.1) channel.2)
    channels

private theorem scalarAt_symm (left right : Nat) :
    RatPolyCoeffEqv (scalarAt left right) (scalarAt right left) := by
  let environment : Nat → RatPoly := fun
    | 0 => (PolyQuaternion.coordinateVariable left).scalar
    | 1 => (PolyQuaternion.coordinateVariable left).iPart
    | 2 => (PolyQuaternion.coordinateVariable left).jPart
    | 3 => (PolyQuaternion.coordinateVariable left).kPart
    | 4 => (PolyQuaternion.coordinateVariable right).scalar
    | 5 => (PolyQuaternion.coordinateVariable right).iPart
    | 6 => (PolyQuaternion.coordinateVariable right).jPart
    | _ => (PolyQuaternion.coordinateVariable right).kPart
  simpa only [scalarAt, PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, environment,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) environment)

private theorem normalizedCharacterAt_symm (left right degree : Nat) :
    RatPolyCoeffEqv (normalizedCharacterAt left right degree)
      (normalizedCharacterAt right left degree) := by
  unfold normalizedCharacterAt
  have hs : RatPolyCoeffEqv (scalarAt left right) (scalarAt right left) :=
    scalarAt_symm left right
  exact (characterPolynomial_coeffEqv hs degree).smul _

theorem normalizedCharacterAt_supported {blocks left right degree : Nat}
    (hl : left < blocks) (hr : right < blocks) :
    SupportedQuaternionBlocks blocks (normalizedCharacterAt left right degree) :=
  by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact character_supported (scalar_supported hl hr) degree s hs

/-- Every valid finite channel product lives on the doubled endpoint carrier. -/
theorem characterProduct_supported (blocks : Nat) : ∀ channels : List (Nat × Nat),
    (∀ channel, channel ∈ channels → channel.1 < blocks) →
    SupportedQuaternionBlocks (blocks+blocks) (characterProduct blocks channels)
  | [], _ => supported_one _
  | channel::channels, hvalid =>
      supported_polyMul
        (normalizedCharacterAt_supported
          (Nat.lt_of_lt_of_le (hvalid channel List.mem_cons_self) (by omega))
          (by have h := hvalid channel List.mem_cons_self; omega))
        (characterProduct_supported blocks channels
          (fun item hi => hvalid item (List.mem_cons_of_mem channel hi)))

private theorem normalized_character_preserves_quadratic {blocks slot degree : Nat}
    (hslot : slot < blocks) {W f : RatPoly}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hpositive : ∀ g, SupportedQuaternionBlocks blocks g →
      (0 : Q') ≤ haarQuadratic blocks W g)
    (hf : SupportedQuaternionBlocks blocks f) :
    (0 : Q') ≤ haarQuadratic blocks
      (polyMul (normalizedCharacterAt slot (blocks+slot) degree) W) f := by
  let c := Q'.ofNat (degree+1)
  let character := characterPolynomial (scalarAt (blocks+slot) slot) degree
  have hcharacter : (0 : Q') ≤ insertion blocks W f character :=
    character_insertion_nonnegative hslot hW hpositive hf degree
  have hc : (0 : Q') ≤ c := Q'.le_of_lt (Q'.ofNat_succ_pos degree)
  have hscaled : (0 : Q') ≤ insertion blocks W f (polySmul c character) :=
    Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hc hcharacter)
      (Q'.ge_of_eqv (insertion_smul blocks W f character c))
  have hsymm : RatPolyCoeffEqv
      (normalizedCharacterAt slot (blocks+slot) degree) (polySmul c character) := by
    exact normalizedCharacterAt_symm slot (blocks+slot) degree
  have he : haarQuadratic blocks
      (polyMul (normalizedCharacterAt slot (blocks+slot) degree) W) f ≈
      insertion blocks W f (polySmul c character) := by
    unfold haarQuadratic insertion
    exact haar_of_coeff
      (((hsymm.mul_right W).mul_right _).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
          (fun
            | 0 => polySmul c character
            | 1 => W
            | _ => polyMul f (liftBoundary blocks f))))
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv he)

/-- Any finite product of valid normalized character channels is positive
semidefinite in the original endpoint Haar quadratic.  Repeated slots are
allowed. -/
theorem characterProduct_quadratic_nonnegative (blocks : Nat) :
    ∀ (channels : List (Nat × Nat)),
      (∀ channel, channel ∈ channels → channel.1 < blocks) →
      ∀ f, SupportedQuaternionBlocks blocks f →
        (0 : Q') ≤ haarQuadratic blocks (characterProduct blocks channels) f
  | [], _, f, hf =>
      Q'.le_trans' _ _ _
        (SumOfSquares.q_mul_self_nonneg (quaternionHaar blocks f))
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
          (haar_split_pairing hf f)))
  | channel::channels, hvalid, f, hf => by
      apply normalized_character_preserves_quadratic
        (hvalid channel List.mem_cons_self)
        (characterProduct_supported blocks channels
          (fun item hi => hvalid item (List.mem_cons_of_mem channel hi)))
        (fun g hg => characterProduct_quadratic_nonnegative blocks channels
          (fun item hi => hvalid item (List.mem_cons_of_mem channel hi)) g hg)
        hf

end YMGap.Continuum.SU2QuaternionCharacterProductPositive

#print axioms YMGap.Continuum.SU2QuaternionCharacterProductPositive.normalizedCharacterAt
#print axioms YMGap.Continuum.SU2QuaternionCharacterProductPositive.characterProduct
#print axioms YMGap.Continuum.SU2QuaternionCharacterProductPositive.characterProduct_supported
#print axioms YMGap.Continuum.SU2QuaternionCharacterProductPositive.characterProduct_quadratic_nonnegative
