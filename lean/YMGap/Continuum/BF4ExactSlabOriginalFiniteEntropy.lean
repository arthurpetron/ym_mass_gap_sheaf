/-
# Finite entropy-polynomial inequality for the ORIGINAL slab action

Apply original finite-product Haar Jensen to the literal full action divided
by H_K(1)^ids.length. The supported polynomial and its pointwise positive
window are constructed from the original heat factors, not supplied as new
analytic premises. All shared link variables and factor multiplicities remain.

The tangent's center is the OWN partition of this identity-normalized action,
Z = Haar(W), not 1. The checked normalizedHeatProductHaar_pin identifies it
with the original partition divided by H_K(1)^ids.length. Nothing here divides
W by Z or calls identity normalization probability normalization.

The entropy stage is the existing finite polynomial partial sum
p_n(t)=sum_{j=1}^n t*(1-t)^j/j. These are finite rational inequalities, not an
identification with logarithmic entropy or a localized partition estimate.
No uniform-volume bound, concentration, physical scaling, H1 or gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
import YMGap.Continuum.QuaternionHaarFiniteEntropy

namespace YMGap.Continuum.BF4ExactSlabOriginalFiniteEntropy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage entropyStage_eval entropyStage_supported)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum partial_nonnegative)

/-- Nonnegative finite entropy partial on the ACTUAL positive original action,
including the zero entropy cutoff. The lower density floor is constructed. -/
theorem original_entropyStage_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) (n : Nat) :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks extent).length
      (entropyStage n (normalizedHeatProduct w hw0 K extent ids)) := by
  apply QuaternionHaarFiniteProductOrder.haar_lower_bound _ _
    (entropyStage_supported (normalizedHeatProduct_supported w hw0 K extent ids) n) 0
  intro qs
  have hb := normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs
  have hn : (0 : Q') ≤ evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt (normalizedFloor_positive hw0 hw1 K ids)) hb.1
  exact Q'.le_trans' _ _ _ (partial_nonnegative _ hn hb.2 n)
    (Q'.ge_of_eqv (entropyStage_eval n _ (environment qs)))

/-- Original finite entropy Jensen with its OWN partition value. The heat
cutoff is K+1; the independent entropy polynomial has n+1 terms. -/
theorem original_partial_jensen {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) (n : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
        (entropyStage (n+1) (normalizedHeatProduct w hw0 K extent ids)) ≤
      partialSum (quaternionHaar (boundaryCompleteSlabLinks extent).length
        (normalizedHeatProduct w hw0 K extent ids)) (n+1) :=
  QuaternionHaarFiniteEntropy.haar_partial_jensen n _ _
    (normalizedHeatProduct_supported w hw0 K extent ids)
    (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).2)

end YMGap.Continuum.BF4ExactSlabOriginalFiniteEntropy

#print axioms YMGap.Continuum.BF4ExactSlabOriginalFiniteEntropy.original_entropyStage_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabOriginalFiniteEntropy.original_partial_jensen
