/-
# A nonzero original plaquette direction missed by one insertion square

For any original finite selected action, any inserted heat factor, and any
two distinct physical fundamental plaquettes, compute two rational
coefficients whose connected pairing with the inserted heat is zero.
The coefficient square budget is strictly positive even when the input
pairings vanish. The original full-action family lower bound certifies
that the resulting polynomial has positive original weighted square norm.

On this direction the insertion response is exactly its third-cumulant
term: the negative square contributes zero. This rules out paying a
positive coefficient fraction using that square alone. It does NOT
assert that the third term is positive, refute a Yang--Mills variance
bound, or prove an OS gap. The computed probe depends on the finite
action and cutoff; no fixed-probe limiting claim is made.
-/

import YMGap.Continuum.RationalOrthogonalPair
import YMGap.Continuum.BF4ExactSlabConnectedResponseLinear
import YMGap.Continuum.BF4ExactSlabTwoPlaquettePositiveNorm

namespace YMGap.Continuum.BF4ExactSlabResponseNullDirection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation (connectedNumerator)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (response thirdNumerator)
open YMGap.Continuum.BF4ExactSlabConnectedResponseLinear
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabTwoPlaquettePositiveNorm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Explicit finite coefficients, not an existential choice of a null vector. -/
def coefficients (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat)
    (p q : Z4Plaq) : Q' × Q' :=
  RationalOrthogonalPair.pair
    (connectedNumerator w K extent ids (faceCharacter extent p) (faceHeatPolynomial w K extent id))
    (connectedNumerator w K extent ids (faceCharacter extent q) (faceHeatPolynomial w K extent id))

/-- Literal finite combination of the two ORIGINAL fundamental characters. -/
def probe (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : Z4Plaq) : RatPoly :=
  let c := coefficients w K extent ids id p q
  twoFaceSpan extent p q c.1 c.2

theorem coefficient_budget_positive (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p q : Z4Plaq) :
    let c := coefficients w K extent ids id p q
    (0 : Q') < c.1*c.1+c.2*c.2 :=
  RationalOrthogonalPair.pair_square_positive _ _

theorem probe_supported (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (probe w K extent ids id p q) :=
  twoFaceSpan_supported extent p q _ _

/-- The SAME old-action connected moment with the actual inserted heat is zero. -/
theorem probe_connected_zero (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p q : Z4Plaq) :
    connectedNumerator w K extent ids (probe w K extent ids id p q)
      (faceHeatPolynomial w K extent id) ≈ 0 :=
  Q'.eqv_trans _ _ _ (connectedNumerator_linear_left w K extent ids _ _ _ _ _)
    (RationalOrthogonalPair.pair_dot_zero _ _)

/-- The null direction is not a zero polynomial hidden behind zero coefficients.
Its square is positive under the FULL original selected action. -/
theorem probe_norm_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (id : Nat) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (hpq : p ≠ q) :
    (0 : Q') < quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (probe w K extent ids id p q) (probe w K extent ids id p q))) :=
  twoFaceSpan_norm_positive hw0 hw1 K extent hK ids hids hnodup hp hq hpq _ _
    (coefficient_budget_positive w K extent ids id p q)

/-- This direction is not merely a constant polynomial, either. This is a
statement about the literal finite polynomial, not an OS quotient. -/
theorem probe_not_constant (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat)
    {p q : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (hpq : p ≠ q) (c : Q') :
    ¬ RatPolyCoeffEqv (probe w K extent ids id p q) (polySmul c polyOne) :=
  twoFaceSpan_not_constant extent hp hq hpq _ _
    (coefficient_budget_positive w K extent ids id p q) c

/-- The entire third-cumulant term remains on this computed signed direction.
No sign or magnitude bound on that term is asserted. -/
theorem probe_response_eq_third (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p q : Z4Plaq) :
    response w K extent ids id (probe w K extent ids id p q) (probe w K extent ids id p q) ≈
      numerator w (B extent) extent ids (faceHeatPolynomial w K extent id) K *
        thirdNumerator w K extent ids (probe w K extent ids id p q)
          (probe w K extent ids id p q) (faceHeatPolynomial w K extent id) :=
  response_eq_third_of_connected_zero w K extent ids id _
    (probe_connected_zero w K extent ids id p q)

/-- One insertion square cannot dominate a positive fraction of every
two-face coefficient budget. The counterdirection is explicitly computed. -/
theorem no_positive_square_fraction (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p q : Z4Plaq) {delta : Q'} (hd : (0 : Q') < delta) :
    let c := coefficients w K extent ids id p q
    let v := connectedNumerator w K extent ids (probe w K extent ids id p q)
      (faceHeatPolynomial w K extent id)
    ¬ delta*(c.1*c.1+c.2*c.2) ≤ v*v := by
  dsimp only
  intro h
  let v := connectedNumerator w K extent ids (probe w K extent ids id p q)
    (faceHeatPolynomial w K extent id)
  have hz := probe_connected_zero w K extent ids id p q
  have hsq : v*v ≈ 0 := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz)
    (Q'.zero_mul_eqv _)
  have hpos := Q'.mul_pos hd (coefficient_budget_positive w K extent ids id p q)
  exact (by decide : ¬ (0 : Q') < 0)
    (Q'.pos_of_lt_of_le hpos (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hsq)))

end YMGap.Continuum.BF4ExactSlabResponseNullDirection

#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.coefficients
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.coefficient_budget_positive
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe_supported
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe_connected_zero
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe_norm_positive
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe_not_constant
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.probe_response_eq_third
#print axioms YMGap.Continuum.BF4ExactSlabResponseNullDirection.no_positive_square_fraction
