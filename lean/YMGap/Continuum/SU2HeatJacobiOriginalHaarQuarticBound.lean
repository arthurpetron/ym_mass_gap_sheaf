/-
# Original Haar quartic comparison from the completed heat profile

The forward original heat margin and the backward computed Bernstein row
meet in the ACTUAL Type-valued Haar square certificate. Coefficient pins
retain the original scalar, inclusive cutoff, and both heat prefixes.
The existing affine consumer then bounds the selected insertion against
the SAME original positive source and odd partition, without a heat-floor
reciprocal. This is not an estimate for a signed centered source or OWN
interacting variance, nor a scaling/survival or continuum mass-gap theorem.
-/

import YMGap.Continuum.SU2HeatJacobiFinitePrefixClassPolynomial
import YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
import YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
import YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison

namespace YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin
open YMGap.Continuum.SU2HeatJacobiFinitePrefixClassPolynomial
open YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (spacingLabelCutoff)
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks oddMass

/-- Both proof directions now construct the actual original polynomial
certificate; no shape witness or Bernstein positivity is supplied. -/
def quarticMarginCertificate {blocks : Nat} {X : RatPoly} {q eta : Q'}
    (P : SquareBound blocks X 1)
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (heta : (0 : Q') < eta)
    (K : Nat) (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1) :
    Certificate blocks (quarticMarginPolynomial q K eta X) := by
  have C := QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate
    (unitArgument X) (unitMarginPolynomial q K eta) eta heta
    (fun y hy0 hy1 => eta_le_unitMargin_eval hq0 hq1 hq heta K hKq hKqq hy0 hy1)
    (unitArgument_certificate P) (oneMinusUnitArgument_certificate P)
  exact .ofCoeff
    (((unitArgument_unshift X (classMarginPolynomial q K eta)).trans
      (subst_classMarginPolynomial X q K eta)).symm) C

/-- Literal squared chord times the ORIGINAL selected heat prefix. -/
def quarticChordInsertion (q : Q') (K : Nat) (X : RatPoly) : RatPoly :=
  let chord := polySmul 2 (polyAdd polyOne (polyNeg X))
  polyMul (polyMul chord chord) (heatPrefix q K X)

/-- Constructed unit square bound for ANY actual relative coordinate pair. -/
def relativeScalarSquare {blocks a b : Nat} (ha : a < blocks) (hb : b < blocks) :
    SquareBound blocks (scalarAt a b) 1 :=
  SquareBound.scalar ((Supported.coordinate ha).mul (Supported.coordinate hb).conj)
    (haarNorm_mul (haarNorm_coordinate ha)
      ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (haarNorm_coordinate hb)))

private theorem coefficient_nonnegative (q : Q') :
    (0 : Q') ≤ quarticProfileCoefficient q :=
  Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg (1-q)))

private theorem error_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (K : Nat) :
    (0 : Q') ≤ quarticPrefixError q K :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide) (spacingClosedTail_nonnegative hq0 _))
    (Q'.mul_nonneg _ _ (coefficient_nonnegative q)
      (spacingClosedTail_nonnegative (HKPos.q_mul_pos hq0 hq0) _))

/-- Selected quartic insertion against the SAME ORIGINAL endpoint source
and unchanged spectator action. No inverse heat minimum or new partition.
The source is positive; signed centered sources are NOT covered. -/
theorem selectedChordInsertion_le_original {q eta : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (heta : (0 : Q') < eta)
    (K width depth i : Nat) (hhead : headCutoff q ≤ K)
    (hKq : spacingLabelCutoff q ≤ K+1)
    (hKqq : spacingLabelCutoff (q*q) ≤ K+1)
    (hi : i ∈ activeBlocks width) :
    selectedInsertion q K width depth i
      (quarticChordInsertion q K (scalarAt (N width+i) i)) ≤
      (quarticProfileCoefficient q+(quarticPrefixError q K+eta))*oddMass q K width depth := by
  have hil := activeBlocks_lt width i hi
  have P : SquareBound (N width+N width) (scalarAt (N width+i) i) 1 :=
    relativeScalarSquare (by omega) (by omega)
  have huw : q*q ≤ q := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0))
    (Q'.le_of_eqv (Q'.mul_one_eqv q))
  exact affine_original_bound hq0 hq1
    (Q'.le_of_lt (HKPos.q_mul_pos hq0 hq0)) huw (coefficient_nonnegative q)
    (Q'.zero_le_add _ _ (error_nonnegative hq0 K) (Q'.le_of_lt heta))
    K width depth i hhead hi
    (quarticChordInsertion q K (scalarAt (N width+i) i))
    (quarticMarginCertificate P hq0 hq1 hq heta K hKq hKqq)

#print axioms quarticMarginCertificate
#print axioms quarticChordInsertion
#print axioms relativeScalarSquare
#print axioms selectedChordInsertion_le_original

end YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound
