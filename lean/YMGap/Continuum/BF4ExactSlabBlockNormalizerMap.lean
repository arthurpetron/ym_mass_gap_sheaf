/-
# The original block normalizer as a bounded positive multiplier

The carrier keeps all original slab coordinates and the exact detached
original action as its weight. The integrated incident collar multiplies on
that same background carrier. These form and norm bounds provide an input to
constructive inversion; no inverse or block conditional projection is claimed.
-/

import YMGap.Continuum.BF4ExactSlabBlockNormalizer
import YMGap.Continuum.PositiveContractionOneStepForm
import YMGap.Continuum.PositiveCoerciveForm
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabBlockNormalizerMap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- The same supported polynomial carrier, weighted by the original detached
action. No links or coordinates are deleted from the carrier. -/
def backgroundData {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (links : List Z4Link) : GNSData :=
  weightedGNSData (blocks extent) (background w K extent links)
    (background_certificate hw0 hw1 K extent hK links)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK links

/-- Multiplication by the actual family-integrated incident collar. -/
def normalizerMap (a : (G).V) : (G).V :=
  ⟨polyMul a.val (normalizer w K extent links),
    supported_polyMul a.property (normalizer_supported w K extent links)⟩

local notation "M" => normalizerMap hw0 hw1 K extent hK links

/-- The multiplier respects supported polynomial differences. -/
theorem normalizerMap_sub (a b : (G).V) :
    (G).veq (M ((G).sub a b)) ((G).sub (M a) (M b)) := by
  change RatPolyCoeffEqv
    (polyMul (polyAdd a.val (polySmul (-1) b.val)) (normalizer w K extent links))
    (polyAdd (polyMul a.val (normalizer w K extent links))
      (polySmul (-1) (polyMul b.val (normalizer w K extent links))))
  rw [polyMul_add_left_exact]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left _ _ _)

/-- The multiplier is symmetric for the exact detached-action form. -/
theorem normalizerMap_symmetric (a b : (G).V) :
    (G).B a (M b) ≈ (G).B (M a) b :=
  haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => a.val | 1 => b.val | _ => normalizer w K extent links)).mul_right _)

/-- Two-sided form bounds for all supported polynomials on the actual
detached-background carrier. -/
theorem normalizerMap_form_bounds
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a : (G).V) :
    blockLower w links.length * (G).B a a ≤ (G).B a (M a) ∧
      (G).B a (M a) ≤ blockUpper w links.length * (G).B a a := by
  have h := normalizer_weighted_bounds hw0 hw1 K extent hK links hl
    (supported_polyMul a.property a.property) (Certificate.square a.val a.property)
  have hp : (G).B a (M a) ≈
      quaternionHaar (blocks extent)
        (polyMul (polyMul (polyMul a.val a.val) (normalizer w K extent links))
          (background w K extent links)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.mul_right _)
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv hp),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.2⟩

/-- Squared multiplier norm ceiling with no pointwise operator order or
spectral theorem. -/
theorem normalizerMap_norm_upper
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a : (G).V) :
    (G).B (M a) (M a) ≤
      (blockUpper w links.length * blockUpper w links.length) * (G).B a a := by
  have hpos (x : (G).V) : (0 : Q') ≤ (G).B x (M x) :=
    Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (blockLower_positive hw0 hw1 links.length))
        ((G).self_nonneg x))
      (normalizerMap_form_bounds hw0 hw1 K extent hK links hl x).1
  exact PositiveContractionOneStepForm.norm_bound G M
    (normalizerMap_symmetric hw0 hw1 K extent hK links) hpos
    (Q'.le_of_lt (blockUpper_positive hw0 links.length))
    (fun x => (normalizerMap_form_bounds hw0 hw1 K extent hK links hl x).2) a

/-- Coercive squared-norm floor on the same background carrier. -/
theorem normalizerMap_norm_lower
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a : (G).V) :
    (blockLower w links.length * blockLower w links.length) * (G).B a a ≤
      (G).B (M a) (M a) :=
  PositiveCoerciveForm.lower_norm G M
    (Q'.le_of_lt (blockLower_positive hw0 hw1 links.length))
    (fun x => (normalizerMap_form_bounds hw0 hw1 K extent hK links hl x).1) a

end YMGap.Continuum.BF4ExactSlabBlockNormalizerMap

#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.backgroundData
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap_sub
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap_norm_upper
#print axioms YMGap.Continuum.BF4ExactSlabBlockNormalizerMap.normalizerMap_norm_lower
