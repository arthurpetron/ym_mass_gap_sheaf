/-
# Original full-replica replacement versus the one-sided star kernel

The insertion contains the SINGLETON-SWAPPED original weight, the full
second complementary action and the actual replacement square. Its
positivity is constructed, not assumed. Exact Haar recoding then applies
the one-sided star comparison to the original full-pair replacement cost.
The right-hand integral still needs its exact exterior/energy Fubini pin.
-/

import YMGap.Continuum.BF4ExactSlabOneSidedStarComparison
import YMGap.Continuum.BF4ExactSlabReplicaPathVariance
import YMGap.Continuum.SU2QuaternionCrossExteriorPair

namespace YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabConditionalStarComparison
open YMGap.Continuum.BF4ExactSlabOneSidedStarComparison
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.SU2QuaternionCrossExteriorPair
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

def headExchange (extent : Nat) (link : Z4Link) :
    QuaternionBlockInvolution (blocks extent + blocks extent) :=
  SU2QuaternionPartialSliceSwap.swap (blocks extent) [slot extent link]

def replacementSquare (extent : Nat) (link : Z4Link) (f : RatPoly) : RatPoly :=
  polyMul (singleBlockDifference (blocks extent) (slot extent link) f)
    (singleBlockDifference (blocks extent) (slot extent link) f)

def replacementIntegral (w : Q') (K extent : Nat) (link : Z4Link) (f : RatPoly) : Q' :=
  quaternionHaar (blocks extent + blocks extent)
    (polyMul (originalPair w K extent) (replacementSquare extent link f))

/-- The weight in the first factor has undergone the selected-head exchange. -/
def replacementInsertion (w : Q') (K extent : Nat) (link : Z4Link) (f : RatPoly) : RatPoly :=
  polyMul (reindexQuaternionPolynomial (headExchange extent link) (fullWeight w K extent))
    (polyMul (liftBoundary (blocks extent) (complementHeat w K extent link))
      (replacementSquare extent link f))

theorem replacement_integral_pin (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    replacementIntegral w K extent link f ≈
      quaternionHaar (blocks extent + blocks extent)
        (polyMul (otherStar w K extent link) (replacementInsertion w K extent link f)) := by
  have h := singleton_pair_square_haar (blocks extent) (slot extent link)
    (List.idxOf_lt_length_of_mem hl) (fullWeight w K extent)
    (incidentHeat w K extent link) (complementHeat w K extent link) f
    (fullWeight_supported w K extent) (incidentHeat_supported w K extent link)
    (complementHeat_supported w K extent link) hf
    (RatPolyCoeffEqv.haarCarrier (heatProduct_partition w K extent link))
    (degree_zero_independent (complementHeat_degree_zero w K extent link hl))
  exact Q'.eqv_trans _ _ _ h (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 1) (.mul (.var 0) (.var 2))) (.var 3))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (by decide)
      (fun | 0 => otherStar w K extent link
           | 1 => reindexQuaternionPolynomial (headExchange extent link) (fullWeight w K extent)
           | 2 => liftBoundary (blocks extent) (complementHeat w K extent link)
           | _ => replacementSquare extent link f)))

def replacementInsertion_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) :
    Certificate (blocks extent + blocks extent) (replacementInsertion w K extent link f) := by
  have hf2 : SupportedQuaternionBlocks (blocks extent + blocks extent) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hd := difference_supported (reindex_supported (headExchange extent link) f) hf2
  have hW := fullWeight_supported w K extent
  have hW2 : SupportedQuaternionBlocks (blocks extent + blocks extent) (fullWeight w K extent) :=
    fun t ht => Nat.le_trans (hW t ht) (Nat.mul_le_mul_left 4 (by omega))
  exact (reindex_certificate (headExchange extent link) hW2
    (certificate_extend (blocks extent) hW (fullWeight_certificate hw0 hw1 K extent hK))).mul
    ((lift_certificate (blocks extent)
      (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
        (fun _ hi => complementIds_physical hi))).mul (.square _ hd))

/-- Literal remaining integral; it has not been renamed as residual energy. -/
def comparisonIntegral {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link) (f : RatPoly) (k : Nat) : Q' :=
  quaternionHaar (blocks extent + blocks extent)
    (polyMul (polyMul (firstKernel hw0 hw1 K extent link k)
      (otherNormalizer w K extent link)) (replacementInsertion w K extent link f))

/-- The independent-full-replica replacement is now on the left of the
actual cross-exterior comparison, with only one finite correction factor. -/
theorem original_replacement_comparison {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (blocks extent) f) (k : Nat) :
    (starLower w extent link * starLower w extent link *
      (1 + -((starRadius hw0 hw1 extent link)^k))) * replacementIntegral w K extent link f ≤
    (starUpper w extent link * starUpper w extent link) *
      comparisonIntegral hw0 hw1 K extent link f k :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (replacement_integral_pin w K extent link hl f hf)))
    (weighted_one_sided_star_comparison hw0 hw1 K extent hK link hl k
      (replacementInsertion_certificate hw0 hw1 K extent hK link f hf))

#print axioms replacement_integral_pin
#print axioms replacementInsertion_certificate
#print axioms original_replacement_comparison

end YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement
