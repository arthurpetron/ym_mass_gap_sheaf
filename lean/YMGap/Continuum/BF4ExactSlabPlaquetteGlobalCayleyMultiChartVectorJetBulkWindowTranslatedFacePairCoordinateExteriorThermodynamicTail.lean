/-
# Volume-free thermodynamic exterior covariance tail

The explicit thermodynamic complement is mapped injectively to its physical
target plaquettes and summed with the four-dimensional L-infinity shell
bound.  The quadratic distance floor from the thermodynamic placement module
therefore converts the finite structural insertion sum into a volume-free
geometric tail.

This module does not yet prove that the scheduled tail tends to zero, prove
convergence of the selected source trajectory, construct a continuum theory
or Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects (amplitude)
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward (listQSum_mul_left)
open YMGap.Continuum.FiniteSelectionMobius (sum_map)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay (blockLength)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv

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

/-- Conservative block-distance floor for the thermodynamic complement. -/
def thermodynamicExteriorBlockFloor
    {w : Q'} (hd : heatRemainderBound w < 1)
    (s L : Nat) : Nat :=
  (thermodynamicExteriorMargin s - (5 * s + 3 * L + 5)) /
    blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4

/-- Explicit target-volume-free covariance budget for the complete
thermodynamic complement. -/
def thermodynamicExteriorCovarianceTailBudget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) : Q' :=
  let P := thermodynamicPlacement s L
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P (s * s) leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    (s * s) leftOffset rightOffset leftFace rightFace
  covarianceAmplitude hd hs carrier cap *
    tailCap (coordinateRateNonnegative hw0 hd) hs
      carrier.animal.support.length
      (thermodynamicExteriorBlockFloor hd s L)

/-- Computed block threshold making the thermodynamic tail at most
`epsilon`. -/
def thermodynamicExteriorCovarianceBlockCutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) (epsilon : Q') : Nat :=
  let P := thermodynamicPlacement s L
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P (s * s) leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    (s * s) leftOffset rightOffset leftFace rightFace
  dyadicBlockCutoff (coordinateRateNonnegative hw0 hd) hs
    carrier.animal.support.length (covarianceAmplitude hd hs carrier cap)
    epsilon

private theorem le_sub_div_of_add_mul_le
    (base block cutoff total : Nat) (hblock : 0 < block)
    (h : base + block * cutoff ≤ total) :
    cutoff ≤ (total - base) / block := by
  apply (Nat.le_div_iff_mul_le hblock).mpr
  rw [Nat.mul_comm]
  omega

/-- An explicit margin condition makes the complete thermodynamic tail at
most `epsilon`. -/
theorem thermodynamicExteriorCovarianceTailBudget_small
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon)
    (hmargin :
      5 * s + 3 * L + 5 +
          blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4 *
            thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs s L
              leftOffset rightOffset leftFace rightFace epsilon ≤
        thermodynamicExteriorMargin s) :
    thermodynamicExteriorCovarianceTailBudget hw0 hd hs s L leftOffset
      rightOffset leftFace rightFace ≤ epsilon := by
  have hfloor :
      thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs s L leftOffset
          rightOffset leftFace rightFace epsilon ≤
        thermodynamicExteriorBlockFloor hd s L := by
    simpa only [thermodynamicExteriorBlockFloor] using
      (le_sub_div_of_add_mul_le
        (5 * s + 3 * L + 5)
        (blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4)
        (thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs s L
          leftOffset rightOffset leftFace rightFace epsilon)
        (thermodynamicExteriorMargin s)
        (PolynomialGeometricDecay.blockLength_pos
          (entropyRate 625 (adjustedCoreRate w hd)) 4)
        hmargin)
  unfold thermodynamicExteriorCovarianceTailBudget
  dsimp only
  apply scaled_tailCap_small_dyadic (coordinateRateNonnegative hw0 hd) hs
  · apply covarianceAmplitudeNonnegative hw0 hd hs
    exact translatedFacePairCapNonnegative
      (thermodynamicPlacement s L) s (s * s) leftOffset rightOffset L
      leftFace rightFace rfl hleftFace hrightFace hleftOffset hrightOffset
  · exact hepsilon
  · simpa only [thermodynamicExteriorCovarianceBlockCutoff] using hfloor

/-- The explicit structural insertion sum from milestone 428 is bounded by a
target-volume-free geometric tail. -/
theorem thermodynamicExteriorCovarianceBudget_le_tail
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    thermodynamicExteriorCovarianceBudget hd hs s L leftOffset rightOffset
        leftFace rightFace ≤
      thermodynamicExteriorCovarianceTailBudget hw0 hd hs s L leftOffset
        rightOffset leftFace rightFace := by
  let P := thermodynamicPlacement s L
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P (s * s) leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    (s * s) leftOffset rightOffset leftFace rightFace
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  let factor := covarianceAmplitude hd hs carrier cap
  let exterior := thermodynamicExteriorIds s L
  let distanceWeight := fun face : Z4Plaq =>
    rate ^ (linfDist carrier.animal.root face -
      carrier.animal.support.length)
  have hfactor : (0 : Q') ≤ factor := by
    apply covarianceAmplitudeNonnegative hw0 hd hs
    exact translatedFacePairCapNonnegative P s (s * s) leftOffset
      rightOffset L leftFace rightFace rfl hleftFace hrightFace
      hleftOffset hrightOffset
  have hfacesNodup :
      (exterior.map (slabPlaquetteAt P.target)).Nodup :=
    CayleyPruferInjection.nodup_map_of_injOn
      (slabPlaquetteAt P.target) exterior
      (thermodynamicExteriorIds_nodup s L)
      (fun left hleft right hright heq =>
        slabPlaquetteAt_injective_on_physical
          (thermodynamicExteriorIds_physical s L left hleft)
          (thermodynamicExteriorIds_physical s L right hright)
          heq)
  have htail := finite_tail_bound
    (coordinateRateNonnegative hw0 hd) hs carrier.animal.root
    carrier.animal.support.length
    (thermodynamicExteriorBlockFloor hd s L)
    (exterior.map (slabPlaquetteAt P.target)) hfacesNodup (by
      intro face hface
      obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
      apply Nat.div_le_div_right
      exact thermodynamic_coordinateCarrier_exterior_exponent_ge
        s L leftOffset rightOffset leftFace rightFace hleftFace hrightFace
        hleftOffset hrightOffset
        (thermodynamicExteriorIds_physical s L id hid)
        (thermodynamicExteriorIds_omitted s L id hid))
  rw [sum_map] at htail
  have hpointwise := sum_le_on
    (coordinateCovarianceInsertionBudget hd hs P (s * s) leftOffset
      rightOffset leftFace rightFace)
    (fun id => factor * distanceWeight (slabPlaquetteAt P.target id))
    exterior (fun id _ => by
      simpa only [coordinateCovarianceInsertionBudget, P, carrier, cap,
        factor, distanceWeight, rate] using
        (Q'.le_of_eqv
          (covarianceBudget_geometric hd hs carrier
            (slabPlaquetteAt P.target id) cap)))
  have htail' :
      listQSum
          (fun id => distanceWeight (slabPlaquetteAt P.target id))
          exterior ≤
        tailCap (coordinateRateNonnegative hw0 hd) hs
          carrier.animal.support.length
          (thermodynamicExteriorBlockFloor hd s L) := by
    simpa only [distanceWeight, rate] using htail
  have hfactorSum :
      listQSum
          (fun id => factor * distanceWeight (slabPlaquetteAt P.target id))
          exterior ≈
        factor *
          listQSum
            (fun id => distanceWeight (slabPlaquetteAt P.target id))
            exterior :=
    listQSum_mul_left factor
      (fun id => distanceWeight (slabPlaquetteAt P.target id)) exterior
  have hresult := Q'.le_trans' _ _ _ hpointwise
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactorSum)
      (Q'.mul_le_mul_of_nonneg_left _ _ factor htail' hfactor))
  simpa only [thermodynamicExteriorCovarianceBudget,
    thermodynamicExteriorCovarianceTailBudget, P, carrier, cap, factor] using
    hresult

private theorem nomeDelta : heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2

private theorem nomeEntropy :
    entropyRate 625 (adjustedCoreRate nome nomeDelta) < 1 :=
  BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2

/-- The actual full thermodynamic covariance versus original selected source
law inherits the volume-free geometric tail. -/
theorem thermodynamicPlacedFullCovariance_source_tail_bound
    (s L leftOffset rightOffset : Nat) (hside : 0 < s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs (CReal.sub
        (thermodynamicPlacedFullCovariance s L leftOffset rightOffset)
        (thermodynamicOriginalSelectedLowerCovariance
          s L leftOffset rightOffset)))
      (ofQ' (thermodynamicExteriorCovarianceTailBudget nome_pos nomeDelta
        nomeEntropy s L leftOffset rightOffset (bulkSourceLowerFace s)
        (bulkSourceLowerFace s))) := by
  apply leEv_trans
    (thermodynamicPlacedFullCovariance_source_structural_bound
      s L leftOffset rightOffset hside hleftOffset hrightOffset)
  apply leEv_of_le
  apply CReal.ofQ'_le_ofQ'
  exact thermodynamicExteriorCovarianceBudget_le_tail nome_pos nomeDelta
    nomeEntropy s L leftOffset rightOffset (bulkSourceLowerFace s)
    (bulkSourceLowerFace s) (bulkSourceLowerFace_mem s hside)
    (bulkSourceLowerFace_mem s hside) hleftOffset hrightOffset

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicExteriorBlockFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicExteriorCovarianceTailBudget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicExteriorCovarianceBlockCutoff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicExteriorCovarianceTailBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicExteriorCovarianceBudget_le_tail
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail.thermodynamicPlacedFullCovariance_source_tail_bound
