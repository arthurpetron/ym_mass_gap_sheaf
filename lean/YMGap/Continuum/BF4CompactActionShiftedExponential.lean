/-
# Positive shifted-exponential quadratic forms for the compact BF4 action

Write the genuine compact coupled action as

  A = 133/4 - D.

`BF4CompactActionSphereShift` proves this identity under exact tenfold Haar
after every polynomial insertion, while `BF4CompactActionCPOrder` proves
that `D` is positive in polynomial-square order.

This file combines those results at every Taylor order.  Given a supported
boundary polynomial `P` and `h = floor (n/2)`, it represents

  P² Dⁿ

as either `(P D^h)²` or `(P D^h)² D`.  Thus every coefficient of the
shifted positive exponential quadratic form is nonnegative, with no degree
or spin cutoff.  A separate evaluation theorem proves that the arranged
carrier is pointwise the advertised polynomial rather than a positivity
surrogate.

## Axiom gate

Finite exact polynomial algebra only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionPhysicalCPOrder

namespace YMGap.Continuum.BF4CompactActionShiftedExponential

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionPhysicalCPOrder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A small exact regrouping identity -/

private def squareProductRegroupLeft : PolyExpr :=
  .mul
    (.mul (.var 0) (.var 1))
    (.mul (.var 0) (.var 1))

private def squareProductRegroupRight : PolyExpr :=
  .mul
    (.mul (.var 0) (.var 0))
    (.mul (.var 1) (.var 1))

private theorem squareProductRegroup_normal :
    normalize squareProductRegroupLeft =
      normalize squareProductRegroupRight := by
  decide

private theorem squareProductRegroup
    (left right : Q') :
    (left * right) * (left * right) ≈
      (left * left) * (right * right) := by
  let rho : Nat → Q' := fun
    | 0 => left
    | _ => right
  simpa [squareProductRegroupLeft,
    squareProductRegroupRight,
    RingNormaliser.eval, rho] using
    (poly_identity_of_normal_eq
      squareProductRegroupLeft
      squareProductRegroupRight
      squareProductRegroup_normal rho)

/-! ## 2. Manifest square carriers for every inserted moment -/

/-- The common polynomial factor `P D^(floor(n/2))`. -/
def compactActionShiftedHalfFactor
    (polynomial : RatPoly) (exponent : Nat) : RatPoly :=
  polyMul polynomial
    (compactActionComplementHalfPower exponent)

/-- Manifest square/square-times-`D` representative of `P² Dⁿ`. -/
def compactActionShiftedMomentSquarePolynomial
    (polynomial : RatPoly) (exponent : Nat) : RatPoly :=
  let factor :=
    compactActionShiftedHalfFactor polynomial exponent
  if exponent % 2 = 0 then
    polyMul factor factor
  else
    polyMul (polyMul factor factor)
      compactActionComplementPolynomial

/-- The manifest carrier stays inside the forty physical quaternion
coordinates whenever the boundary insertion does. -/
theorem compactActionShiftedMomentSquarePolynomial_supported
    {polynomial : RatPoly}
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (exponent : Nat) :
    SupportedQuaternionBlocks 10
      (compactActionShiftedMomentSquarePolynomial
        polynomial exponent) := by
  let half :=
    compactActionComplementHalfPower exponent
  let factor :=
    compactActionShiftedHalfFactor polynomial exponent
  have hhalf :
      SupportedQuaternionBlocks 10 half := by
    exact polynomialPower_supported
      compactActionComplementPolynomial_supported
      (exponent / 2)
  have hfactor :
      SupportedQuaternionBlocks 10 factor := by
    exact supported_polyMul hsupport hhalf
  unfold compactActionShiftedMomentSquarePolynomial
  split
  · exact supported_polyMul hfactor hfactor
  · exact supported_polyMul
      (supported_polyMul hfactor hfactor)
      compactActionComplementPolynomial_supported

/-- Pointwise identification of the manifest carrier with the genuine
inserted complement moment `(P·P) Dⁿ`. -/
theorem eval_compactActionShiftedMomentSquarePolynomial
    (rho : Nat → Q') (polynomial : RatPoly)
    (exponent : Nat) :
    evalRatPoly rho
        (compactActionShiftedMomentSquarePolynomial
          polynomial exponent) ≈
      (evalRatPoly rho polynomial *
          evalRatPoly rho polynomial) *
        qpow
          (evalRatPoly rho
            compactActionComplementPolynomial)
          exponent := by
  let p := evalRatPoly rho polynomial
  let d :=
    evalRatPoly rho compactActionComplementPolynomial
  let halfIndex := exponent / 2
  let half :=
    compactActionComplementHalfPower exponent
  let factor :=
    compactActionShiftedHalfFactor polynomial exponent
  have hhalf :
      evalRatPoly rho half ≈
        qpow d halfIndex := by
    exact eval_polynomialPower
      rho compactActionComplementPolynomial halfIndex
  have hfactor :
      evalRatPoly rho factor ≈
        p * qpow d halfIndex := by
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_mul rho polynomial half) ?_
    exact Q'.mul_eqv_congr_left p _ _ hhalf
  have hfactorSquare :
      evalRatPoly rho factor *
          evalRatPoly rho factor ≈
        (p * qpow d halfIndex) *
          (p * qpow d halfIndex) := by
    refine Q'.eqv_trans _
      ((p * qpow d halfIndex) *
        evalRatPoly rho factor) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hfactor
    · exact Q'.mul_eqv_congr_left _ _ _ hfactor
  unfold compactActionShiftedMomentSquarePolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    refine Q'.eqv_trans _
      (evalRatPoly rho factor *
        evalRatPoly rho factor) _
      (evalRatPoly_mul rho factor factor) ?_
    refine Q'.eqv_trans _
      ((p * qpow d halfIndex) *
        (p * qpow d halfIndex)) _ ?_ ?_
    · exact hfactorSquare
    refine Q'.eqv_trans _
      ((p * p) *
        (qpow d halfIndex *
          qpow d halfIndex)) _
      (squareProductRegroup p
        (qpow d halfIndex)) ?_
    refine Q'.eqv_trans _
      ((p * p) *
        qpow d (halfIndex + halfIndex)) _
      (Q'.mul_eqv_congr_left (p * p) _ _
        (Q'.eqv_symm
          (qpow_add d halfIndex halfIndex))) ?_
    rw [hexponent]
    exact Q'.eqv_refl _
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    refine Q'.eqv_trans _
      ((evalRatPoly rho factor *
          evalRatPoly rho factor) * d) _ ?_ ?_
    · refine Q'.eqv_trans _
        (evalRatPoly rho
          (polyMul factor factor) *
            evalRatPoly rho
              compactActionComplementPolynomial) _
        (evalRatPoly_mul rho
          (polyMul factor factor)
          compactActionComplementPolynomial) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (evalRatPoly_mul rho factor factor)
    refine Q'.eqv_trans _
      (((p * qpow d halfIndex) *
          (p * qpow d halfIndex)) * d) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        hfactorSquare
    refine Q'.eqv_trans _
      (((p * p) *
          (qpow d halfIndex *
            qpow d halfIndex)) * d) _
      (Q'.mul_eqv_congr_right _ _ _
        (squareProductRegroup p
          (qpow d halfIndex))) ?_
    refine Q'.eqv_trans _
      (((p * p) *
          qpow d (halfIndex + halfIndex)) * d) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (p * p) _ _
          (Q'.eqv_symm
            (qpow_add d halfIndex halfIndex)))) ?_
    refine Q'.eqv_trans _
      ((p * p) *
        (qpow d (halfIndex + halfIndex) * d)) _
      (Q'.mul_assoc_eqv
        (p * p)
        (qpow d (halfIndex + halfIndex)) d) ?_
    have hpower :
        qpow d (halfIndex + halfIndex) * d =
          qpow d (halfIndex + halfIndex + 1) := rfl
    rw [hpower, hexponent]
    exact Q'.eqv_refl _

/-! ## 3. Complete positivity at every shifted Taylor order -/

/-- **All-label, all-degree shifted moment positivity.**

For every supported physical boundary polynomial `P`,

  `0 ≤ H_10(P² Dⁿ)`.

The proof is literally a Haar square in even degree and the already-proved
BF4 complement CP order in odd degree.
-/
theorem compactActionShiftedMomentSquare_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (exponent : Nat) :
    (0 : Q') ≤
      tenfoldHaar
        (compactActionShiftedMomentSquarePolynomial
          polynomial exponent) := by
  let half :=
    compactActionComplementHalfPower exponent
  let factor :=
    compactActionShiftedHalfFactor polynomial exponent
  have hhalf :
      SupportedQuaternionBlocks 10 half := by
    exact polynomialPower_supported
      compactActionComplementPolynomial_supported
      (exponent / 2)
  have hfactor :
      SupportedQuaternionBlocks 10 factor :=
    supported_polyMul hsupport hhalf
  unfold compactActionShiftedMomentSquarePolynomial
  split
  · exact tenfoldHaar_square_nonnegative
      factor hfactor
  · exact compactActionComplement_cp
      factor hfactor

/-! ## 4. Positive Taylor quadratics -/

/-- The `n`-th rational quadratic coefficient in the positive expansion
`H(P² exp(D))`.  `termAbs 1 n` is exactly `1/n!`. -/
def compactActionShiftedTaylorQuadraticTerm
    (polynomial : RatPoly) (exponent : Nat) : Q' :=
  ExpNeg.termAbs 1 exponent *
    tenfoldHaar
      (compactActionShiftedMomentSquarePolynomial
        polynomial exponent)

theorem compactActionShiftedTaylorQuadraticTerm_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (exponent : Nat) :
    (0 : Q') ≤
      compactActionShiftedTaylorQuadraticTerm
        polynomial exponent := by
  exact Q'.mul_nonneg _ _
    (ExpNeg.termAbs_nonneg 1 (by decide) exponent)
    (compactActionShiftedMomentSquare_nonnegative
      polynomial hsupport exponent)

/-- The first `terms` shifted-exponential quadratic coefficients. -/
def compactActionShiftedTaylorQuadraticPartial
    (polynomial : RatPoly) : Nat → Q'
  | 0 => 0
  | terms + 1 =>
      compactActionShiftedTaylorQuadraticPartial
          polynomial terms +
        compactActionShiftedTaylorQuadraticTerm
          polynomial terms

/-- Every finite shifted-exponential quadratic partial is positive
semidefinite on the full supported polynomial carrier. -/
theorem compactActionShiftedTaylorQuadraticPartial_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    ∀ terms : Nat,
      (0 : Q') ≤
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms
  | 0 => Q'.le_refl' 0
  | terms + 1 =>
      Q'.zero_le_add _ _
        (compactActionShiftedTaylorQuadraticPartial_nonnegative
          polynomial hsupport terms)
        (compactActionShiftedTaylorQuadraticTerm_nonnegative
          polynomial hsupport terms)

/-- Adding one Taylor coefficient can only increase the positive shifted
quadratic partial. -/
theorem compactActionShiftedTaylorQuadraticPartial_monotone
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms : Nat) :
    compactActionShiftedTaylorQuadraticPartial
        polynomial terms ≤
      compactActionShiftedTaylorQuadraticPartial
        polynomial (terms + 1) := by
  exact Q'.add_le_self_of_nonneg _ _
    (compactActionShiftedTaylorQuadraticTerm_nonnegative
      polynomial hsupport terms)

end YMGap.Continuum.BF4CompactActionShiftedExponential

#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.squareProductRegroup
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.compactActionShiftedMomentSquarePolynomial_supported
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.eval_compactActionShiftedMomentSquarePolynomial
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.compactActionShiftedMomentSquare_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.compactActionShiftedTaylorQuadraticTerm_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.compactActionShiftedTaylorQuadraticPartial_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionShiftedExponential.compactActionShiftedTaylorQuadraticPartial_monotone
