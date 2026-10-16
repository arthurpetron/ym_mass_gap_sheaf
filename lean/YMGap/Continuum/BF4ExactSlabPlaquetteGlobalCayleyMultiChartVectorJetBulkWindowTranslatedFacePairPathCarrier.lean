/-
# One connected path carrier for a translated vector-jet face pair

An explicit plaquette adjacency path between the two literal translated target
faces now supplies the single connected `ProbeCarrier` required by the guarded
covariance-response theorem.  Both local vector-character factors lift to the
common appended four-link list, and the carrier support costs at most one more
face than the supplied path length.

This module does not yet construct the coordinate path, prove its quantitative
length from the bulk-source coordinates, insert exterior action faces, sum a
boundary telescope, or prove a continuum or mass-gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
import YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SepLatticeZ4Linf

/-- The exact common four-link list of the two translated target faces. -/
def translatedOriginalBulkVectorQuadraticJetFacePairLinks
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) : List Z4Link :=
  edgesOf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace) ++
    edgesOf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace)

/-- Compile one supplied endpoint-to-endpoint plaquette path into the common
carrier of the two translated local factors. -/
def translatedOriginalBulkVectorQuadraticJetFacePairCarrier
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (path : AdjPath z4SepLinf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace)) :
    ProbeCarrier
      (translatedOriginalBulkVectorQuadraticJetFacePairLinks
        P n leftOffset rightOffset leftFace rightFace) := by
  exact pairCarrier path

/-- The common carrier pays only the supplied corridor length. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (path : AdjPath z4SepLinf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace)) :
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
      P n leftOffset rightOffset leftFace rightFace path).animal.support.length ≤
        path.pathLen + 1 :=
  pairCarrier_support_length_le path

/-- Any explicit corridor-length cap transfers directly to carrier size. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le_of_pathLen
    (P : Placement) (n leftOffset rightOffset corridor : Nat)
    (leftFace rightFace : Z4Plaq)
    (path : AdjPath z4SepLinf
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetPlacedFace
        P n rightOffset rightFace))
    (hpath : path.pathLen ≤ corridor) :
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier
      P n leftOffset rightOffset leftFace rightFace path).animal.support.length ≤
        corridor + 1 :=
  Nat.le_trans
    (translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le
      P n leftOffset rightOffset leftFace rightFace path)
    (Nat.add_le_add_right hpath 1)

/-- The left translated local factor is local on the common pair carrier. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePair_left_local
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) :
    LinkLocal P.target
      (translatedOriginalBulkVectorQuadraticJetFacePairLinks
        P n leftOffset rightOffset leftFace rightFace)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        P n leftOffset leftFace) := by
  exact left_local_on_pair
    (translatedOriginalBulkVectorQuadraticJetFace_local
      P n leftOffset leftFace)

/-- The right translated local factor is local on the common pair carrier. -/
theorem translatedOriginalBulkVectorQuadraticJetFacePair_right_local
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) :
    LinkLocal P.target
      (translatedOriginalBulkVectorQuadraticJetFacePairLinks
        P n leftOffset rightOffset leftFace rightFace)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        P n rightOffset rightFace) := by
  exact right_local_on_pair
    (translatedOriginalBulkVectorQuadraticJetFace_local
      P n rightOffset rightFace)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePairLinks
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePairCarrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePairCarrier_support_length_le_of_pathLen
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePair_left_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier.translatedOriginalBulkVectorQuadraticJetFacePair_right_local
