/-
# Exterior polynomial approximants to the actual block conditional update

The finite inverse iteration applied to N_p remains independent of every
integrated coordinate. Its division error is controlled by the ORIGINAL
full-action norm of p, with an explicit relative tolerance cutoff depending
only on nome, block size and tolerance. No limiting projection, inter-block
angle, physical scaling or OS gap is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
import YMGap.Continuum.BF4ExactSlabBlockInsertedNorm

namespace YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockInsertedNorm
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)

/-- No integrated coordinate is reintroduced by the polynomial division. -/
theorem approximateInverse_independent (r : (G).V)
    (hr : ∀ i, i ∈ slots extent links → QuaternionBlockIndependent i r.val) :
    ∀ n i, i ∈ slots extent links → QuaternionBlockIndependent i (A r n).val
  | 0, i, _ => quaternionBlockIndependent_polySmul 0 (quaternionBlockIndependent_polyOne i)
  | n+1, i, hi =>
      quaternionBlockIndependent_polyAdd (approximateInverse_independent r hr n i hi)
        (quaternionBlockIndependent_polySmul _
          (quaternionBlockIndependent_polyAdd (hr i hi)
            (quaternionBlockIndependent_polySmul (-1)
              (quaternionBlockIndependent_polyMul
                (approximateInverse_independent r hr n i hi)
                (normalizer_independent w K extent links i hi)))))

def numeratorVector (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) : (G).V :=
  ⟨insertedNormalizer w K extent links p, insertedNormalizer_supported w K extent links hp⟩

/-- Actual polynomial approximants to N_p/D; the original numerator is data. -/
def conditionalApproximation (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (n : Nat) : (G).V :=
  A (numeratorVector hw0 hw1 K extent hK links p hp) n

theorem conditionalApproximation_independent (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (n i : Nat) (hi : i ∈ slots extent links) :
    QuaternionBlockIndependent i (conditionalApproximation hw0 hw1 K extent hK links p hp n).val :=
  approximateInverse_independent hw0 hw1 K extent hK links _
    (insertedNormalizer_independent w K extent links p) n i hi

/-- The error is measured in the background form; the right side retains
the SAME original full-action norm of p. -/
theorem conditionalApproximation_defect_norm
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) (n : Nat) :
    let r := numeratorVector hw0 hw1 K extent hK links p hp
    let a := conditionalApproximation hw0 hw1 K extent hK links p hp n
    (G).B ((G).sub r (M a)) ((G).sub r (M a)) ≤
      ((inverseRate w links.length * inverseRate w links.length)^n * blockUpper w links.length) *
        weightedPair blocks (fullWeight w K extent) p p := by
  have hq := (inverseRate_bounds hw0 hw1 links.length).1
  exact Q'.le_trans' _ _ _
    (approximateInverse_residual_norm hw0 hw1 K extent hK links hl _ n)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (insertedNormalizer_weighted_norm hw0 hw1 K extent hK links hl p hp)
      (Q'.pow_nonneg _ (Q'.mul_nonneg _ _ hq hq) n))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))

/-- A relative squared-error cutoff independent of extent, cutoff and p. -/
def relativeCutoff (w : Q') (size : Nat) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w size * inverseRate w size) (blockUpper w size) epsilon

theorem conditionalApproximation_relative_error
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : relativeCutoff w links.length epsilon ≤ n) :
    let r := numeratorVector hw0 hw1 K extent hK links p hp
    let a := conditionalApproximation hw0 hw1 K extent hK links p hp n
    (G).B ((G).sub r (M a)) ((G).sub r (M a)) ≤
      epsilon * weightedPair blocks (fullWeight w K extent) p p := by
  have hq := inverseRate_bounds hw0 hw1 links.length
  have hq2 : inverseRate w links.length * inverseRate w links.length < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  have hb := PositiveContractionResidual.geometric_bound
    (Q'.mul_nonneg _ _ hq.1 hq.1) hq2
    (Q'.le_of_lt (blockUpper_positive hw0 links.length)) hepsilon n hn
  have hpos : (0 : Q') ≤ weightedPair blocks (fullWeight w K extent) p p :=
    (BF4ExactSlabStarFullActionProbe.fullData hw0 hw1 K extent hK).self_nonneg ⟨p,hp⟩
  exact Q'.le_trans' _ _ _
    (conditionalApproximation_defect_norm hw0 hw1 K extent hK links hl p hp n)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hb hpos)

#print axioms approximateInverse_independent
#print axioms numeratorVector
#print axioms conditionalApproximation
#print axioms conditionalApproximation_independent
#print axioms conditionalApproximation_defect_norm
#print axioms relativeCutoff
#print axioms conditionalApproximation_relative_error

end YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
