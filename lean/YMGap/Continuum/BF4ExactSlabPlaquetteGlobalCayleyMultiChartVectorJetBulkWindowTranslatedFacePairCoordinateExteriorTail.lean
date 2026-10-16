/-
# Volume-uniform exterior covariance tail

The sequential exterior telescope is combined with the existing four-
dimensional L-infinity shell count.  Every omitted target face has the checked
coordinate-carrier exponent floor, while each one-face covariance budget is
the same fixed amplitude times the corresponding geometric distance power.
Consequently the entire finite exterior insertion list has a bound independent
of the target slab extent and heat cutoff.

The endpoint action remains in selected-then-exterior order.  This module does
not yet prove permutation invariance of the normalized covariance, identify
that endpoint with the canonical full-action law, remove volume, construct a
continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope
import YMGap.Continuum.Z4LinfGeometricSum

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects (amplitude)
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_mul_left)
open YMGap.Continuum.FiniteSelectionMobius (sum_map)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay (blockLength)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv

private theorem appendPhysicalList {extent : Nat} {base extra : List Nat}
    (hbase : ∀ id, id ∈ base → id ∈ slabPhysicalFaceEdges extent)
    (hextra : ∀ id, id ∈ extra → id ∈ slabPhysicalFaceEdges extent) :
    ∀ id, id ∈ base ++ extra → id ∈ slabPhysicalFaceEdges extent := by
  intro id hid
  rcases List.mem_append.mp hid with hid | hid
  · exact hbase id hid
  · exact hextra id hid

private theorem coordinateRateNonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _)
    (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

private theorem summedDefectAmplitudeNonnegative
    {w c b : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {left : List Z4Link} (P : ProbeCarrier left)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ amplitude P w hd hs c b := by
  unfold amplitude
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ hc hb)
          (Q'.mul_nonneg _ _ hc hb))
        (probePrefactor_nonnegative w hd _))
      (ClusterCount.ofNat_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem covarianceAmplitudeNonnegative
    {w c : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {left : List Z4Link} (P : ProbeCarrier left)
    (hc : (0 : Q') ≤ c) :
    (0 : Q') ≤ covarianceAmplitude hd hs P c := by
  unfold covarianceAmplitude
  have hinv : (0 : Q') ≤ inverseFaceFloor w hd :=
    Q'.le_of_lt (inverseFaceFloor_pos w hd)
  have hprefix : (0 : Q') ≤ prefixCap w := prefixCap_nonnegative hw0
  have hsquare : (0 : Q') ≤ c * c := Q'.mul_nonneg _ _ hc hc
  have hlarge := Q'.mul_nonneg _ _
    (summedDefectAmplitudeNonnegative hd hs P hsquare hprefix) hinv
  have hsmall := Q'.mul_nonneg _ _
    (summedDefectAmplitudeNonnegative hd hs P hc hprefix) hinv
  exact Q'.zero_le_add _ _ hlarge
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ hc hsmall)
      (Q'.mul_nonneg _ _ hc hsmall))

private theorem translatedFacePairCapNonnegative
    (P : Placement) (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    (0 : Q') ≤ translatedOriginalBulkVectorQuadraticJetFacePairCap
      n leftOffset rightOffset leftFace rightFace :=
  (translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
    P s n leftOffset rightOffset L leftFace rightFace hsource
    hleftFace hrightFace hleftOffset hrightOffset).nonnegative

/-- Conservative block-distance floor inherited from the explicit exterior
exponent lower bound. -/
def coordinateExteriorBlockFloor
    {w : Q'} (hd : heatRemainderBound w < 1)
    (s n L : Nat) : Nat :=
  (Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s) -
      (5 * s + 3 * L + 5)) /
    blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4

/-- Explicit volume-free sum budget for every omitted action face. -/
def coordinateExteriorCovarianceTailBudget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq) : Q' :=
  let P := zeroPlacement s n L target hroom
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P n leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    n leftOffset rightOffset leftFace rightFace
  covarianceAmplitude hd hs carrier cap *
    tailCap (coordinateRateNonnegative hw0 hd) hs
      carrier.animal.support.length (coordinateExteriorBlockFloor hd s n L)

/-- Computed block threshold at which the complete exterior covariance tail
is at most `epsilon`.  All carrier-size and covariance-amplitude dependence is
kept visible in this threshold. -/
def coordinateExteriorCovarianceBlockCutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq) (epsilon : Q') : Nat :=
  let P := zeroPlacement s n L target hroom
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P n leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    n leftOffset rightOffset leftFace rightFace
  dyadicBlockCutoff (coordinateRateNonnegative hw0 hd) hs
    carrier.animal.support.length (covarianceAmplitude hd hs carrier cap) epsilon

private theorem le_sub_div_of_add_mul_le
    (base block cutoff total : Nat) (hblock : 0 < block)
    (h : base + block * cutoff ≤ total) :
    cutoff ≤ (total - base) / block := by
  apply (Nat.le_div_iff_mul_le hblock).mpr
  rw [Nat.mul_comm]
  omega

/-- An explicit collar condition makes the entire volume-free exterior budget
at most `epsilon`.  This theorem exposes rather than hides the dependence of
the required collar on the concrete carrier and covariance amplitude. -/
theorem coordinateExteriorCovarianceTailBudget_small
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon)
    (hcollar :
      5 * s + 3 * L + 5 +
          blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4 *
            coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
              rightOffset L target hroom leftFace rightFace epsilon ≤
        Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s)) :
    coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
      rightOffset L target hroom leftFace rightFace ≤ epsilon := by
  have hfloor :
      coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
          rightOffset L target hroom leftFace rightFace epsilon ≤
        coordinateExteriorBlockFloor hd s n L := by
    simpa only [coordinateExteriorBlockFloor] using
      (le_sub_div_of_add_mul_le
        (5 * s + 3 * L + 5)
        (blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4)
        (coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
          rightOffset L target hroom leftFace rightFace epsilon)
        (Nat.min n (originalBulkVectorQuadraticJetSpatialCollar s))
        (PolynomialGeometricDecay.blockLength_pos
          (entropyRate 625 (adjustedCoreRate w hd)) 4)
        hcollar)
  unfold coordinateExteriorCovarianceTailBudget
  dsimp only
  apply scaled_tailCap_small_dyadic (coordinateRateNonnegative hw0 hd) hs
  · apply covarianceAmplitudeNonnegative hw0 hd hs
    exact translatedFacePairCapNonnegative
      (zeroPlacement s n L target hroom) s n leftOffset rightOffset L
      leftFace rightFace rfl hleftFace hrightFace hleftOffset hrightOffset
  · exact hepsilon
  · simpa only [coordinateExteriorCovarianceBlockCutoff] using hfloor

/-- The structural sum of all canonical omitted-face insertion budgets has no
target-volume factor. -/
theorem zeroPlacement_coordinateCovarianceInsertionBudget_sum_le_tail
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    listQSum
        (coordinateCovarianceInsertionBudget hd hs
          (zeroPlacement s n L target hroom) n leftOffset rightOffset
          leftFace rightFace)
        (zeroPlacementExteriorIds s n L target hroom) ≤
      coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace := by
  let P := zeroPlacement s n L target hroom
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P n leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    n leftOffset rightOffset leftFace rightFace
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  let factor := covarianceAmplitude hd hs carrier cap
  let exterior := zeroPlacementExteriorIds s n L target hroom
  let distanceWeight := fun face : Z4Plaq =>
    rate ^ (linfDist carrier.animal.root face - carrier.animal.support.length)
  have hfactor : (0 : Q') ≤ factor := by
    apply covarianceAmplitudeNonnegative hw0 hd hs
    exact translatedFacePairCapNonnegative P s n leftOffset rightOffset L
      leftFace rightFace rfl hleftFace hrightFace hleftOffset hrightOffset
  have hfacesNodup : (exterior.map (slabPlaquetteAt target)).Nodup :=
    CayleyPruferInjection.nodup_map_of_injOn
      (slabPlaquetteAt target) exterior
      (zeroPlacementExteriorIds_nodup s n L target hroom)
      (fun left hleft right hright heq =>
        slabPlaquetteAt_injective_on_physical
          (zeroPlacementExteriorIds_physical s n L target hroom left hleft)
          (zeroPlacementExteriorIds_physical s n L target hroom right hright)
          heq)
  have htail := finite_tail_bound
    (coordinateRateNonnegative hw0 hd) hs carrier.animal.root
    carrier.animal.support.length (coordinateExteriorBlockFloor hd s n L)
    (exterior.map (slabPlaquetteAt target)) hfacesNodup (by
      intro face hface
      obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
      apply Nat.div_le_div_right
      exact zeroPlacement_coordinateCarrier_exterior_exponent_ge
        s n leftOffset rightOffset L target hroom leftFace rightFace
        hleftFace hrightFace hleftOffset hrightOffset
        (zeroPlacementExteriorIds_physical s n L target hroom id hid)
        (zeroPlacementExteriorIds_omitted s n L target hroom id hid))
  rw [sum_map] at htail
  have hpointwise := sum_le_on
    (coordinateCovarianceInsertionBudget hd hs P n leftOffset rightOffset
      leftFace rightFace)
    (fun id => factor * distanceWeight (slabPlaquetteAt target id))
    exterior (fun id _ => by
      simpa only [coordinateCovarianceInsertionBudget, P, carrier, cap,
        factor, distanceWeight, rate] using
        (Q'.le_of_eqv
          (covarianceBudget_geometric hd hs carrier
            (slabPlaquetteAt target id) cap)))
  have htail' :
      listQSum
          (fun id => distanceWeight (slabPlaquetteAt target id)) exterior ≤
        tailCap (coordinateRateNonnegative hw0 hd) hs
          carrier.animal.support.length
          (coordinateExteriorBlockFloor hd s n L) := by
    simpa only [distanceWeight, rate] using htail
  have hfactorSum :
      listQSum
          (fun id => factor * distanceWeight (slabPlaquetteAt target id))
          exterior ≈
        factor *
          listQSum (fun id => distanceWeight (slabPlaquetteAt target id))
            exterior :=
    listQSum_mul_left factor
      (fun id => distanceWeight (slabPlaquetteAt target id)) exterior
  have hresult := Q'.le_trans' _ _ _ hpointwise
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactorSum)
      (Q'.mul_le_mul_of_nonneg_left _ _ factor htail' hfactor))
  simpa only [coordinateExteriorCovarianceTailBudget, P, carrier, cap,
    factor] using hresult

/-- The finite selected-to-complete-order covariance telescope inherits the
volume-free exterior tail budget. -/
theorem finite_covariance_zeroPlacement_exterior_tail_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (stage : Nat) :
    Q'.abs
      (finiteCovariance w hw0 hw1 target
          (selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L) ++
            zeroPlacementExteriorIds s n L target hroom)
          (appendPhysicalList
            (selectedIds_physical (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L)
              (originalBulkVectorQuadraticJetIds_physical_at_placement
                (zeroPlacement s n L target hroom) s n L rfl))
            (zeroPlacementExteriorIds_physical s n L target hroom))
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n rightOffset rightFace) stage +
        -(finiteCovariance w hw0 hw1 target
          (selectedIds (zeroPlacement s n L target hroom)
            (originalBulkVectorQuadraticJetIds s n L))
          (selectedIds_physical (zeroPlacement s n L target hroom)
            (originalBulkVectorQuadraticJetIds s n L)
            (originalBulkVectorQuadraticJetIds_physical_at_placement
              (zeroPlacement s n L target hroom) s n L rfl))
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n rightOffset rightFace) stage)) ≤
      coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace := by
  exact Q'.le_trans' _ _ _
    (finite_covariance_zeroPlacement_exterior_telescope hw0 hw1 hsmall hd hs
      s n leftOffset rightOffset L target hroom leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset stage)
    (zeroPlacement_coordinateCovarianceInsertionBudget_sum_le_tail hw0 hd hs
      s n leftOffset rightOffset L target hroom leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.coordinateExteriorBlockFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.coordinateExteriorCovarianceTailBudget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.coordinateExteriorCovarianceBlockCutoff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.coordinateExteriorCovarianceTailBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.zeroPlacement_coordinateCovarianceInsertionBudget_sum_le_tail
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail.finite_covariance_zeroPlacement_exterior_tail_bound
