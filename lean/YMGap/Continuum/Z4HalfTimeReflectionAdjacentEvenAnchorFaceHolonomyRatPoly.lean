/-
# Polynomial pullback of the adjacent-even anchor face to four edge variables

The local anchor-face SOS has now been realized by explicit polynomials in the
four coordinates of one unit quaternion, and the standard oriented plaquette
holonomy has been realized by four polynomials in sixteen edge coordinates.
This leaf composes those two constructions with the checked arbitrary-variable
`RatPoly` substitution.

The substitution sends local coordinates `0,1,2,3` to the scalar-first
components of

    U0 * U3 * conj(U2) * conj(U1),

and sends every unused local coordinate to zero.  Each local feature and the
assembled weighted-SOS polynomial therefore becomes a literal polynomial in
the sixteen edge coordinates.  Evaluation is proved first against the
holonomy anchor input, then against the pulled-back finite SOS, and finally
against the physical truncated face class value.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.RationalQuaternionRatPoly
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.RatPolySubstitution
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition
open YMGap.RepTheory

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Compatibility of the two sixteen-coordinate environments -/

/-- The list-based four-edge environment from the geometric pullback agrees
pointwise with the pattern-matching environment used to evaluate the
quaternion holonomy polynomial. -/
theorem fourEdgeEnvironments_agree (input : FourOrientedEdgeInput) :
    ∀ coordinate : Nat,
      Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input coordinate =
        RationalQuaternionRatPoly.fourEdgeEnvironment
          input.u0.val input.u1.val input.u2.val input.u3.val coordinate
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ
      (Nat.succ (Nat.succ (Nat.succ (Nat.succ
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ
          (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))))))))))) => rfl

/-- The holonomy polynomial evaluates correctly in the geometric pullback's
official sixteen-coordinate environment. -/
theorem eval_orientedPlaquetteHolonomyPolynomial_fourEdgeEnvironment
    (input : FourOrientedEdgeInput) :
    (RationalQuaternionRatPoly.eval
      (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
        input)
      orientedPlaquetteHolonomyPolynomial).Equivalent
        (standardPlaquetteHolonomy input).val := by
  let geometricEnvironment : Nat → Q' :=
    Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
      input
  let polynomialEnvironment : Nat → Q' :=
    RationalQuaternionRatPoly.fourEdgeEnvironment
      input.u0.val input.u1.val input.u2.val input.u3.val
  have henvironment : ∀ coordinate,
      geometricEnvironment coordinate ≈ polynomialEnvironment coordinate :=
    fun coordinate =>
      Q'.eqv_of_eq (fourEdgeEnvironments_agree input coordinate)
  have htransport :
      (RationalQuaternionRatPoly.eval geometricEnvironment
        orientedPlaquetteHolonomyPolynomial).Equivalent
      (RationalQuaternionRatPoly.eval polynomialEnvironment
        orientedPlaquetteHolonomyPolynomial) :=
    ⟨evalRatPoly_environment_congr henvironment
        orientedPlaquetteHolonomyPolynomial.r,
      evalRatPoly_environment_congr henvironment
        orientedPlaquetteHolonomyPolynomial.i,
      evalRatPoly_environment_congr henvironment
        orientedPlaquetteHolonomyPolynomial.j,
      evalRatPoly_environment_congr henvironment
        orientedPlaquetteHolonomyPolynomial.k⟩
  exact RationalQuaternion.semanticSetoid.iseqv.trans htransport
    (eval_orientedPlaquetteHolonomyPolynomial
      input.u0.val input.u1.val input.u2.val input.u3.val)

/-! ## 2. The local-to-edge substitution -/

/-- Replace the four local anchor variables by the four components of the
standard oriented plaquette holonomy polynomial.  Coordinates outside the
local four-coordinate carrier are sent to zero. -/
def anchorToFourEdgeSubstitution : Nat → RatPoly
  | 0 => orientedPlaquetteHolonomyPolynomial.r
  | 1 => orientedPlaquetteHolonomyPolynomial.i
  | 2 => orientedPlaquetteHolonomyPolynomial.j
  | 3 => orientedPlaquetteHolonomyPolynomial.k
  | _ => polyZero

/-- Evaluation of the substitution coordinate map is precisely the local
anchor environment of the standard unit-norm plaquette holonomy. -/
theorem eval_anchorToFourEdgeSubstitution
    (input : FourOrientedEdgeInput) : ∀ coordinate : Nat,
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorToFourEdgeSubstitution coordinate) ≈
      anchorEnvironment (plaquetteHolonomyInput input) coordinate := by
  have hholonomy :=
    eval_orientedPlaquetteHolonomyPolynomial_fourEdgeEnvironment input
  intro coordinate
  rcases coordinate with _ | coordinate
  · exact hholonomy.1
  rcases coordinate with _ | coordinate
  · exact hholonomy.2.1
  rcases coordinate with _ | coordinate
  · exact hholonomy.2.2.1
  rcases coordinate with _ | coordinate
  · exact hholonomy.2.2.2
  exact Q'.eqv_refl _

/-! ## 3. Feature and complete-face polynomial pullbacks -/

/-- One selected anchor-face feature, pulled back to sixteen edge
coordinates. -/
def anchorFaceHolonomyFeaturePolynomial (cutoff term : Nat) : RatPoly :=
  substitute anchorToFourEdgeSubstitution
    (anchorFaceFeaturePolynomial cutoff term)

/-- The complete weighted anchor-face SOS polynomial, pulled back to sixteen
edge coordinates. -/
def anchorFaceHolonomyWeightedSOSPolynomial (cutoff : Nat) : RatPoly :=
  substitute anchorToFourEdgeSubstitution
    (anchorFaceWeightedSOSPolynomial cutoff)

/-- Evaluation of a pulled-back feature is the corresponding local feature at
the standard plaquette holonomy input. -/
theorem eval_anchorFaceHolonomyFeaturePolynomial_local
    (cutoff term : Nat) (input : FourOrientedEdgeInput) :
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyFeaturePolynomial cutoff term) ≈
      (anchorFaceSOS cutoff).feature term (plaquetteHolonomyInput input) := by
  exact Q'.eqv_trans _ _ _
    (eval_substitute anchorToFourEdgeSubstitution
      (anchorFaceFeaturePolynomial cutoff term)
      (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
        input))
    (Q'.eqv_trans _ _ _
      (evalRatPoly_environment_congr
        (eval_anchorToFourEdgeSubstitution input)
        (anchorFaceFeaturePolynomial cutoff term))
      (eval_anchorFaceFeaturePolynomial cutoff term
        (plaquetteHolonomyInput input)))

/-- The same feature theorem stated directly for the finite SOS pulled back to
the four oriented edges. -/
theorem eval_anchorFaceHolonomyFeaturePolynomial
    (cutoff term : Nat) (input : FourOrientedEdgeInput) :
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyFeaturePolynomial cutoff term) ≈
      (anchorFaceHolonomySOS cutoff).feature term input := by
  change
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyFeaturePolynomial cutoff term) ≈
      (anchorFaceSOS cutoff).feature term (plaquetteHolonomyInput input)
  exact eval_anchorFaceHolonomyFeaturePolynomial_local cutoff term input

/-- Evaluation of the substituted complete-face polynomial is the local
weighted SOS value at the standard plaquette holonomy. -/
theorem eval_anchorFaceHolonomyWeightedSOSPolynomial_local
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyWeightedSOSPolynomial cutoff) ≈
      value (anchorFaceSOS cutoff) (plaquetteHolonomyInput input) := by
  exact Q'.eqv_trans _ _ _
    (eval_substitute anchorToFourEdgeSubstitution
      (anchorFaceWeightedSOSPolynomial cutoff)
      (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
        input))
    (Q'.eqv_trans _ _ _
      (evalRatPoly_environment_congr
        (eval_anchorToFourEdgeSubstitution input)
        (anchorFaceWeightedSOSPolynomial cutoff))
      (eval_anchorFaceWeightedSOSPolynomial cutoff
        (plaquetteHolonomyInput input)))

/-- The literal sixteen-coordinate polynomial evaluates to the corresponding
four-edge pullback SOS value. -/
theorem eval_anchorFaceHolonomyWeightedSOSPolynomial
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyWeightedSOSPolynomial cutoff) ≈
      value (anchorFaceHolonomySOS cutoff) input := by
  exact Q'.eqv_trans _ _ _
    (eval_anchorFaceHolonomyWeightedSOSPolynomial_local cutoff input)
    (Q'.eqv_symm
      (value_pullback plaquetteHolonomyInput (anchorFaceSOS cutoff) input))

/-- Direct physical evaluation theorem for the substituted complete-face
polynomial. -/
theorem eval_anchorFaceHolonomyWeightedSOSPolynomial_eqv_classValue
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyWeightedSOSPolynomial cutoff) ≈
      anchorTruncatedFaceClassValue cutoff
        (standardPlaquetteHolonomy input).val.r := by
  exact Q'.eqv_trans _ _ _
    (eval_anchorFaceHolonomyWeightedSOSPolynomial cutoff input)
    (value_anchorFaceHolonomySOS cutoff input)

/-- The orientation matching the preceding local polynomial bridge: the
physical truncated class value is extensionally the explicit substituted
sixteen-coordinate polynomial. -/
theorem anchorTruncatedFaceClassValue_eqv_eval_anchorFaceHolonomyPolynomial
    (cutoff : Nat) (input : FourOrientedEdgeInput) :
    anchorTruncatedFaceClassValue cutoff
        (standardPlaquetteHolonomy input).val.r ≈
      evalRatPoly
        (Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          input)
        (anchorFaceHolonomyWeightedSOSPolynomial cutoff) :=
  Q'.eqv_symm
    (eval_anchorFaceHolonomyWeightedSOSPolynomial_eqv_classValue cutoff input)

#print axioms fourEdgeEnvironments_agree
#print axioms eval_orientedPlaquetteHolonomyPolynomial_fourEdgeEnvironment
#print axioms eval_anchorToFourEdgeSubstitution
#print axioms eval_anchorFaceHolonomyFeaturePolynomial
#print axioms eval_anchorFaceHolonomyWeightedSOSPolynomial
#print axioms anchorTruncatedFaceClassValue_eqv_eval_anchorFaceHolonomyPolynomial

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly
