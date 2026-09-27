/-
# Exact exterior pairing for the original block normalizer

The family insertion of an exterior-independent source is multiplication by
the actual integrated collar. Thus the original full-action form, restricted
to two exterior-independent supported inputs, is the detached-background
form paired with that same multiplier. This is a finite exact identity, not
an inverse, conditional projection, angle bound, or continuum statement.
-/

import YMGap.Continuum.BF4ExactSlabBlockInsertedNorm

namespace YMGap.Continuum.BF4ExactSlabBlockExteriorPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInsertedNorm
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Pull an independent exterior polynomial through the exact original
family integration. No supportedness or positivity premise is needed for
this coefficient identity. -/
theorem insertedNormalizer_of_independent (w : Q') (K extent : Nat)
    (links : List Z4Link) (r : RatPoly)
    (hr : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i r) :
    RatPolyCoeffEqv (insertedNormalizer w K extent links r)
      (polyMul r (normalizer w K extent links)) :=
  familyProject_mul_of_independent (slots extent links) r
    (collarHeat w K extent links) hr

/-- The exact original pairing on two family-independent supported inputs
equals the detached-background pairing with its actual block normalizer
multiplier. The background carrier retains every original coordinate. -/
theorem original_exterior_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K)
    (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a b : (backgroundData hw0 hw1 K extent hK links).V)
    (ha : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i a.val)
    (hb : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i b.val) :
    (fullData hw0 hw1 K extent hK).B a b ≈
      (backgroundData hw0 hw1 K extent hK links).B a
        (normalizerMap hw0 hw1 K extent hK links b) := by
  let B := background w K extent links
  let N := normalizer w K extent links
  have hpair := insertedNormalizer_pair_pin w K extent links hl a.val b.val ha
  have hnum := insertedNormalizer_of_independent w K extent links b.val hb
  change weightedPair (blocks extent) (fullWeight w K extent) a.val b.val ≈
    weightedPair (blocks extent) B a.val (polyMul b.val N)
  exact Q'.eqv_trans _ _ _ hpair
    (haar_of_coeff (((RatPolyCoeffEqv.refl a.val).mul hnum).mul_right B))

end YMGap.Continuum.BF4ExactSlabBlockExteriorPairing

#print axioms YMGap.Continuum.BF4ExactSlabBlockExteriorPairing.insertedNormalizer_of_independent
#print axioms YMGap.Continuum.BF4ExactSlabBlockExteriorPairing.original_exterior_pair
