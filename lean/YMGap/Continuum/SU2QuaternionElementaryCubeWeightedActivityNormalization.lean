/-
# Weighted elementary-cube Haar activity and the factor-sixteen fence

The canonical six-face trace product has normalized Haar value `1/16`.
Selecting the fundamental character on all six heat-kernel faces therefore
has weight

    (coeffW coupling 1)^6 * (1/16).

The older `canonicalSurfaceActivity` carrier instead multiplies the six face
coefficients by the *cardinality* of each link invariant space.  On the
bivalent elementary cube every such cardinality is one, so its coarse and
centered scalar formulas are `(coeffW coupling 1)^6`.  They contain no Schur
kernel or closed index-loop normalization.

This leaf records the mismatch without mutating that widely used production
surrogate.  It proves scalar linearity for the honest complex polynomial Haar
carrier, constructs the weighted canonical cube, and compares its exact
scalar value with the coarse and centered surrogate activities.  These are
scalar normalization fences, not yet geometric representative-identification
theorems and not a universal correction for arbitrary surfaces.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionElementaryCubeCanonicalTraceExpansionProduct
import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity

namespace YMGap.Continuum.SU2QuaternionElementaryCubeWeightedActivityNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionElementaryCubeCanonicalTraceExpansionProduct
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Real scalar multiplication in the honest complex carrier -/

private theorem q_neg_zero_eqv : (-(0 : Q')) ≈ 0 := by
  decide

/-- Embed an exact rational scalar as a real constant complex polynomial. -/
def complexRatPolyRealScalar (scalar : Q') : ComplexRatPoly :=
  (polyConst scalar, polyZero)

/-- Componentwise exact-rational scaling of an honest complex polynomial. -/
def complexRatPolyRealSmul
    (scalar : Q') (value : ComplexRatPoly) : ComplexRatPoly :=
  (polySmul scalar value.1, polySmul scalar value.2)

private theorem polyMul_polyConst_left (scalar : Q') :
    forall polynomial : RatPoly,
      polyMul (polyConst scalar) polynomial =
        polySmul scalar polynomial
  | [] => rfl
  | term :: polynomial => by
      change (term.1, scalar * term.2) ::
          polyMul (polyConst scalar) polynomial =
        (term.1, scalar * term.2) :: polySmul scalar polynomial
      rw [polyMul_polyConst_left scalar polynomial]

/-- Raw structural identity: left multiplication by a real constant complex
polynomial is componentwise scalar multiplication.  This is equality in the
duplicate-preserving carrier, not an appeal to polynomial extensionality. -/
theorem complexRatPolyRealScalar_mul (scalar : Q') :
    forall value : ComplexRatPoly,
      complexRatPolyMul (complexRatPolyRealScalar scalar) value =
        complexRatPolyRealSmul scalar value
  | (real, imaginary) => by
      change
        (polyAdd (polyMul (polyConst scalar) real)
            (polyNeg (polyMul polyZero imaginary)),
          polyAdd (polyMul (polyConst scalar) imaginary)
            (polyMul polyZero real)) =
          (polySmul scalar real, polySmul scalar imaginary)
      rw [polyMul_polyConst_left, polyMul_polyConst_left]
      simp [polyZero, polyMul, polyNeg, polyAdd]

/-- Multiplying a rational-complex value by a real scalar has the expected
componentwise value. -/
theorem rationalComplexMul_real_left_eqv
    (scalar : Q') (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul (scalar, 0) value)
      (scalar * value.1, scalar * value.2) := by
  unfold rationalComplexMul RationalComplexEqv
  constructor
  · refine Q'.eqv_trans _ (scalar * value.1 + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv value.2))
          q_neg_zero_eqv)
    · exact YMGap.Constructive.QPoly.q_add_zero_eqv _
  · refine Q'.eqv_trans _ (scalar * value.2 + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv value.1)
    · exact YMGap.Constructive.QPoly.q_add_zero_eqv _

/-- Real-by-real rational-complex multiplication remains purely real. -/
theorem rationalComplexMul_real_real_eqv (scalar real : Q') :
    RationalComplexEqv
      (rationalComplexMul (scalar, 0) (real, 0))
      (scalar * real, 0) :=
  rationalComplexEqv_trans
    (rationalComplexMul_real_left_eqv scalar (real, 0))
    ⟨Q'.eqv_refl _, Q'.mul_zero_eqv scalar⟩

/-- Finite-product Haar is linear under componentwise real scaling of an
honest complex polynomial. -/
theorem finiteProductHaarComplex_realSmul
    (blockCount : Nat) (scalar : Q') (value : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyRealSmul scalar value))
      (rationalComplexMul (scalar, 0)
        (finiteProductHaarComplex blockCount value)) := by
  unfold finiteProductHaarComplex complexRatPolyRealSmul
  refine rationalComplexEqv_trans
    (show RationalComplexEqv
      (finiteProductHaar blockCount (polySmul scalar value.1),
       finiteProductHaar blockCount (polySmul scalar value.2))
      (scalar * finiteProductHaar blockCount value.1,
       scalar * finiteProductHaar blockCount value.2) from
      ⟨finiteProductHaar_smul blockCount scalar value.1,
       finiteProductHaar_smul blockCount scalar value.2⟩) ?_
  exact rationalComplexEqv_symm
    (rationalComplexMul_real_left_eqv scalar
      (finiteProductHaar blockCount value.1,
       finiteProductHaar blockCount value.2))

/-- Equivalent scalar-linearity interface using literal multiplication by a
real constant polynomial. -/
theorem finiteProductHaarComplex_realScalar_mul
    (blockCount : Nat) (scalar : Q') (value : ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul (complexRatPolyRealScalar scalar) value))
      (rationalComplexMul (scalar, 0)
        (finiteProductHaarComplex blockCount value)) := by
  rw [complexRatPolyRealScalar_mul]
  exact finiteProductHaarComplex_realSmul blockCount scalar value

/-! ## 2. The honestly weighted canonical cube -/

/-- The normalized Haar factor of the elementary-cube boundary network. -/
def elementaryCubeHaarNormalization : Q' :=
  Q'.mkPos 1 16 (by decide)

/-- The selected six-fundamental-face heat-kernel coefficient multiplying
the canonical all-standard cube trace product. -/
def radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct
    (coupling : Q') : ComplexRatPoly :=
  complexRatPolyMul
    (complexRatPolyRealScalar ((coeffW coupling 1) ^ 6))
    radiusZeroElementaryCubeCanonicalTraceExpansionProduct

/-- **Exact weighted canonical cube value.**  Six fundamental character
coefficients multiply the normalized Haar factor `1/16`. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct
          coupling))
      (((coeffW coupling 1) ^ 6) * elementaryCubeHaarNormalization, 0) := by
  unfold radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_realScalar_mul
      (adjacentEvenActiveLinks 0).length ((coeffW coupling 1) ^ 6)
      radiusZeroElementaryCubeCanonicalTraceExpansionProduct) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right (((coeffW coupling 1) ^ 6), 0)
      finiteProductHaarComplex_radiusZeroElementaryCubeCanonicalTraceExpansionProduct_exact) ?_
  unfold elementaryCubeHaarNormalization
  exact rationalComplexMul_real_real_eqv
    ((coeffW coupling 1) ^ 6) (Q'.mkPos 1 16 (by decide))

/-! ## 3. Scalar comparison with the production surrogate -/

/-- Apply the elementary-cube Haar normalization to a scalar activity.  This
operation is intentionally cube-specific; it is not a definition for general
surface topology or higher-valence links. -/
def elementaryCubeHaarNormalizeActivity (activity : Q') : Q' :=
  activity * elementaryCubeHaarNormalization

/-- The cube-specific normalization is exactly inverted by multiplication
by sixteen. -/
theorem elementaryCubeHaarNormalizeActivity_mul_sixteen
    (activity : Q') :
    elementaryCubeHaarNormalizeActivity activity * (16 : Q') ≈ activity := by
  unfold elementaryCubeHaarNormalizeActivity elementaryCubeHaarNormalization
  refine Q'.eqv_trans _
    (activity * (Q'.mkPos 1 16 (by decide) * (16 : Q'))) _
    (Q'.mul_assoc_eqv activity (Q'.mkPos 1 16 (by decide)) (16 : Q')) ?_
  refine Q'.eqv_trans _ (activity * 1) _
    (Q'.mul_eqv_congr_left activity _ _ (by decide))
    (Q'.mul_one_eqv activity)

/-- Haar-normalized scalar attached to the coarse box-2 cube support. -/
def coarseUnitCubeCanonicalSurfaceHaarActivity (coupling : Q') : Q' :=
  elementaryCubeHaarNormalizeActivity
    (canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds)

/-- Haar-normalized scalar attached to the centered box-3 cube support. -/
def centeredCoarseUnitCubeCanonicalSurfaceHaarActivity
    (coupling : Q') : Q' :=
  elementaryCubeHaarNormalizeActivity
    (canonicalSurfaceActivity coupling 3
      centeredCoarseUnitCubeRootAtThree)

/-- Scalar normalization fence for the coarse support.  This compares exact
values; it does not yet identify the two geometric representatives. -/
theorem finiteProductHaarComplex_weightedCanonical_eq_coarseActivity_div_sixteen
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct
          coupling))
      (coarseUnitCubeCanonicalSurfaceHaarActivity coupling, 0) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact
      coupling) ?_
  constructor
  · unfold coarseUnitCubeCanonicalSurfaceHaarActivity
      elementaryCubeHaarNormalizeActivity
    exact Q'.mul_eqv_congr_right _ _ elementaryCubeHaarNormalization
      (Q'.eqv_symm
        (coarseUnitCube_canonicalSurfaceActivity_eqv coupling))
  · exact Q'.eqv_refl 0

/-- Scalar normalization fence for the centered support.  The same factor is
recovered after translating the combinatorial cube carrier. -/
theorem finiteProductHaarComplex_weightedCanonical_eq_centeredActivity_div_sixteen
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct
          coupling))
      (centeredCoarseUnitCubeCanonicalSurfaceHaarActivity coupling, 0) := by
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact
      coupling) ?_
  constructor
  · unfold centeredCoarseUnitCubeCanonicalSurfaceHaarActivity
      elementaryCubeHaarNormalizeActivity
    exact Q'.mul_eqv_congr_right _ _ elementaryCubeHaarNormalization
      (Q'.eqv_symm
        (centeredCoarseUnitCube_canonicalSurfaceActivity_eqv coupling))
  · exact Q'.eqv_refl 0

/-- The old coarse production scalar is exactly sixteen times its
cube-Haar-normalized correction.  It remains a useful combinatorial
surrogate, but is not the normalized cube character-sector value. -/
theorem coarseUnitCubeCanonicalSurfaceHaarActivity_mul_sixteen_eqv_surrogate
    (coupling : Q') :
    coarseUnitCubeCanonicalSurfaceHaarActivity coupling * (16 : Q') ≈
      canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds := by
  unfold coarseUnitCubeCanonicalSurfaceHaarActivity
  exact elementaryCubeHaarNormalizeActivity_mul_sixteen _

/-- Centered form of the exact factor-sixteen surrogate fence. -/
theorem centeredCoarseUnitCubeCanonicalSurfaceHaarActivity_mul_sixteen_eqv_surrogate
    (coupling : Q') :
    centeredCoarseUnitCubeCanonicalSurfaceHaarActivity coupling * (16 : Q') ≈
      canonicalSurfaceActivity coupling 3
        centeredCoarseUnitCubeRootAtThree := by
  unfold centeredCoarseUnitCubeCanonicalSurfaceHaarActivity
  exact elementaryCubeHaarNormalizeActivity_mul_sixteen _

#print axioms complexRatPolyRealScalar_mul
#print axioms rationalComplexMul_real_left_eqv
#print axioms rationalComplexMul_real_real_eqv
#print axioms finiteProductHaarComplex_realSmul
#print axioms finiteProductHaarComplex_realScalar_mul
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact
#print axioms elementaryCubeHaarNormalizeActivity_mul_sixteen
#print axioms finiteProductHaarComplex_weightedCanonical_eq_coarseActivity_div_sixteen
#print axioms finiteProductHaarComplex_weightedCanonical_eq_centeredActivity_div_sixteen
#print axioms coarseUnitCubeCanonicalSurfaceHaarActivity_mul_sixteen_eqv_surrogate
#print axioms centeredCoarseUnitCubeCanonicalSurfaceHaarActivity_mul_sixteen_eqv_surrogate

end YMGap.Continuum.SU2QuaternionElementaryCubeWeightedActivityNormalization
