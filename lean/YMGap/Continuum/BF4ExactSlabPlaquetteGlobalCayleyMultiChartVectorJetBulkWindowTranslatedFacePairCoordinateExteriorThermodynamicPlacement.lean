/-
# Thermodynamic odd-slab placement of the lower vector-jet face pair

Translate the complete selected vector-jet source into an explicit odd slab
so that its listed lower face lands at the symmetric thermodynamic coordinate
`3*s^2`.  The two translated local factors are then the fixed lower
plaquette expressions from the ordinary covariance sequence.

This is an exact carrier and finite-law identification.  It does not yet
bound the exterior target action, prove convergence of the selected source
trajectory, take a continuum limit, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison (expectation_prefix)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay (shiftedCharacter)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4FiniteBoxExhaustion

/-- Symmetric margin used to receive the translated scheduled source. -/
def thermodynamicMargin (s : Nat) : Nat := 3 * (s * s)

/-- Odd full-action target supporting the thermodynamic presentation. -/
def thermodynamicTarget (s L : Nat) : Nat :=
  centralExtent (L + thermodynamicMargin s)

private theorem bulkSourceOffset_le_square (s : Nat) :
    bulkSourceOffset s ≤ s * s := by
  unfold bulkSourceOffset
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

/-- Explicit anisotropic placement of the canonical selected source into the
odd thermodynamic target. -/
def thermodynamicPlacement (s L : Nat) : Placement where
  source := originalBulkVectorQuadraticJetExtent s (s * s) L
  target := thermodynamicTarget s L
  space := thermodynamicMargin s - bulkSourceOffset s
  time := thermodynamicMargin s - s * s
  space_room := by
    have hoffset := bulkSourceOffset_le_square s
    have hspace : thermodynamicMargin s - bulkSourceOffset s ≤
        thermodynamicMargin s := Nat.sub_le _ _
    unfold originalBulkVectorQuadraticJetExtent
      SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainderExtent
      thermodynamicTarget thermodynamicMargin centralExtent
    omega
  time_room := by
    unfold originalBulkVectorQuadraticJetExtent
      SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainderExtent
      thermodynamicTarget thermodynamicMargin centralExtent
    omega

theorem thermodynamicPlacement_source (s L : Nat) :
    (thermodynamicPlacement s L).source =
      originalBulkVectorQuadraticJetExtent s (s * s) L := rfl

theorem thermodynamicPlacement_target (s L : Nat) :
    (thermodynamicPlacement s L).target = thermodynamicTarget s L := rfl

/-- Fixed base face at a chronological offset inside base half `L`. -/
def baseLowerFace (offset : Nat) : Z4Plaq :=
  ((0, 0, 0, offset), .p01)

theorem baseLowerFace_physical (L offset : Nat) (hoffset : offset ≤ L) :
    baseLowerFace offset ∈ boundaryCompleteSlabPlaquettes (centralExtent L) := by
  unfold boundaryCompleteSlabPlaquettes
  apply List.mem_filter.mpr
  constructor
  · unfold boxPlaquettes
    apply List.mem_flatMap.mpr
    refine ⟨(0, 0, 0, offset), ?_, ?_⟩
    · unfold boxVertices
      apply List.mem_flatMap.mpr
      refine ⟨0, List.mem_range.mpr (by unfold centralExtent; omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨0, List.mem_range.mpr (by unfold centralExtent; omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨0, List.mem_range.mpr (by unfold centralExtent; omega), ?_⟩
      exact List.mem_map.mpr
        ⟨offset, List.mem_range.mpr (by unfold centralExtent; omega), rfl⟩
    · apply List.mem_map.mpr
      refine ⟨.p01, ?_, rfl⟩
      exact List.mem_cons_self
  · apply decide_eq_true
    unfold baseLowerFace centralExtent plaquetteTimeAdmissible
    dsimp only [dirsOf]
    omega

/-- Computed physical ID of the fixed base face. -/
def baseLowerFaceId (L offset : Nat) : Nat :=
  listIndexOf (baseLowerFace offset)
    (boundaryCompleteSlabPlaquettes (centralExtent L))

theorem baseLowerFaceId_physical (L offset : Nat) (hoffset : offset ≤ L) :
    baseLowerFaceId L offset ∈ slabPhysicalFaceEdges (centralExtent L) := by
  apply List.mem_range.mpr
  exact listIndexOf_lt_of_mem _ _ (baseLowerFace_physical L offset hoffset)

theorem baseLowerFaceId_pin (L offset : Nat) (hoffset : offset ≤ L) :
    slabPlaquetteAt (centralExtent L) (baseLowerFaceId L offset) =
      baseLowerFace offset := by
  exact getD_listIndexOf_of_mem _ _ _ (baseLowerFace_physical L offset hoffset)

theorem baseLowerFaceId_lower (L offset : Nat) (hoffset : offset ≤ L) :
    baseLowerFaceId L offset ∈ centralLowerFaceIds L := by
  apply mem_centralLowerFaceIds.mpr
  constructor
  · exact baseLowerFaceId_physical L offset hoffset
  · rw [baseLowerFaceId_pin L offset hoffset]
    unfold baseLowerFace plaquetteHalfSide spatialHalfSide
    simp only [if_pos hoffset]

private def termExpression {half id : Nat}
    (hid : id ∈ centralLowerFaceIds half) :
    List (Nat × Q') → PlaquetteExpression half
  | [] => .smul 0 .unit
  | term :: terms =>
      .add (.smul term.2 (.character id hid term.1))
        (termExpression hid terms)

private theorem termExpression_evaluate {half id : Nat}
    (hid : id ∈ centralLowerFaceIds half) (F : Nat → Nat → RatPoly) :
    ∀ terms : List (Nat × Q'),
      RatPolyCoeffEqv (evaluate F (termExpression hid terms))
        (BF4ExactPhysicalCenteredVacuumHaarResummation.finitePolySum
          (fun term => polySmul term.2 (F id term.1)) terms)
  | [] => RatPolyCoeffEqv.zero_smul polyOne
  | _term :: terms =>
      (RatPolyCoeffEqv.refl _).add
        (termExpression_evaluate hid F terms)

/-- Fixed lower expression representing the local vector quadratic jet. -/
def vectorJetLowerExpression (L offset : Nat) (hoffset : offset ≤ L) :
    PlaquetteExpression L :=
  termExpression (baseLowerFaceId_lower L offset hoffset)
    vectorQuadraticJetTerms

theorem shifted_vectorJetLowerExpression_pin
    (s L offset : Nat) (hoffset : offset ≤ L) :
    RatPolyCoeffEqv
      (shiftedExpression (thermodynamicMargin s)
        (vectorJetLowerExpression L offset hoffset))
      (sweptProduct (thermodynamicTarget s L) 0
        [(shiftFace (thermodynamicMargin s) (thermodynamicMargin s)
          (baseLowerFace offset), vectorQuadraticJetTerms)]) := by
  have hsum := termExpression_evaluate
    (baseLowerFaceId_lower L offset hoffset)
    (fun id spin => shiftedCharacter L (thermodynamicMargin s)
      (slabPlaquetteAt (centralExtent L) id) spin)
    vectorQuadraticJetTerms
  rw [baseLowerFaceId_pin L offset hoffset] at hsum
  rw [swept_zero]
  change RatPolyCoeffEqv _
    (polyMul
      (BF4ExactPhysicalCenteredVacuumHaarResummation.finitePolySum
        (fun term => polySmul term.2
          (characterPolynomial
            (correctedSlabPlaquettePolynomial (thermodynamicTarget s L)
              (shiftFace (thermodynamicMargin s) (thermodynamicMargin s)
                (baseLowerFace offset))).scalar term.1))
        vectorQuadraticJetTerms)
      polyOne)
  exact hsum.trans
    (YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.mul_one _).symm

/-- The translated scheduled lower face lands exactly on the symmetric face
used by the fixed-expression thermodynamic sequence. -/
theorem thermodynamicPlacement_lowerFace_pin
    (s L offset : Nat) :
    translatedOriginalBulkVectorQuadraticJetPlacedFace
        (thermodynamicPlacement s L) (s * s) offset
        (bulkSourceLowerFace s) =
      shiftFace (thermodynamicMargin s) (thermodynamicMargin s)
        (baseLowerFace offset) := by
  have hoffset : bulkSourceOffset s ≤ thermodynamicMargin s := by
    exact Nat.le_trans (bulkSourceOffset_le_square s) (by
      unfold thermodynamicMargin
      omega)
  have hoffset' : bulkSourceOffset s ≤ 3 * (s * s) := by
    simpa only [thermodynamicMargin] using hoffset
  have hsquare : s * s ≤ 3 * (s * s) := by omega
  have htime :
      s * s + offset + (3 * (s * s) - s * s) =
        offset + 3 * (s * s) := by
    calc
      _ = offset + (s * s + (3 * (s * s) - s * s)) := by ac_rfl
      _ = offset + 3 * (s * s) := by
        rw [Nat.add_sub_of_le hsquare]
  unfold translatedOriginalBulkVectorQuadraticJetPlacedFace
    originalBulkVectorQuadraticJetPlacedFace bulkSourceLowerFace
    thermodynamicPlacement thermodynamicMargin baseLowerFace
    timeShiftPlaquette timeShiftVertex shiftFace shiftVertex
  dsimp only
  simp only [Nat.zero_add, Nat.add_sub_of_le hoffset', htime]

/-- The literal translated local factor is coefficientwise the fixed lower
thermodynamic expression at margin `3*s^2`. -/
theorem translatedLowerFacePlaced_expression_pin
    (s L offset : Nat) (hoffset : offset ≤ L) :
    RatPolyCoeffEqv
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        (thermodynamicPlacement s L) (s * s) offset
        (bulkSourceLowerFace s))
      (shiftedExpression (thermodynamicMargin s)
        (vectorJetLowerExpression L offset hoffset)) := by
  unfold translatedOriginalBulkVectorQuadraticJetFacePlaced
  rw [thermodynamicPlacement_lowerFace_pin s L offset]
  exact (shifted_vectorJetLowerExpression_pin s L offset hoffset).symm

/-- Full original-action covariance in the thermodynamic target of the two
literal translated lower-face factors. -/
def thermodynamicPlacedFullCovariance
    (s L leftOffset rightOffset : Nat) : CReal :=
  covariance nome nome_pos nome_lt_one (thermodynamicTarget s L)
    (slabPhysicalFaceEdges (thermodynamicTarget s L)) (fun _ hid => hid)
    (translatedOriginalBulkVectorQuadraticJetFacePlaced
      (thermodynamicPlacement s L) (s * s) leftOffset
      (bulkSourceLowerFace s))
    (translatedOriginalBulkVectorQuadraticJetFacePlaced
      (thermodynamicPlacement s L) (s * s) rightOffset
      (bulkSourceLowerFace s))

/-- The full covariance in the translated odd target is exactly the fixed
ordinary lower covariance sequence term. -/
theorem thermodynamicPlacedFullCovariance_sequence_pin
    (s L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    Equiv (thermodynamicPlacedFullCovariance s L leftOffset rightOffset)
      (lowerCovarianceSequence
        (vectorJetLowerExpression L leftOffset hleftOffset)
        (vectorJetLowerExpression L rightOffset hrightOffset)
        (thermodynamicMargin s)) := by
  let p := translatedOriginalBulkVectorQuadraticJetFacePlaced
    (thermodynamicPlacement s L) (s * s) leftOffset
    (bulkSourceLowerFace s)
  let q := translatedOriginalBulkVectorQuadraticJetFacePlaced
    (thermodynamicPlacement s L) (s * s) rightOffset
    (bulkSourceLowerFace s)
  let ep := shiftedExpression (thermodynamicMargin s)
    (vectorJetLowerExpression L leftOffset hleftOffset)
  let eq := shiftedExpression (thermodynamicMargin s)
    (vectorJetLowerExpression L rightOffset hrightOffset)
  have hp : RatPolyCoeffEqv p ep := by
    exact translatedLowerFacePlaced_expression_pin s L leftOffset hleftOffset
  have hq : RatPolyCoeffEqv q eq := by
    exact translatedLowerFacePlaced_expression_pin s L rightOffset hrightOffset
  have hpair := BF4ExactSlabPolynomialExpectation.expectation_congr nome nome_pos nome_lt_one
    (L + thermodynamicMargin s) (hp.mul hq)
  have hleft := BF4ExactSlabPolynomialExpectation.expectation_congr nome nome_pos nome_lt_one
    (L + thermodynamicMargin s) hp
  have hright := BF4ExactSlabPolynomialExpectation.expectation_congr nome nome_pos nome_lt_one
    (L + thermodynamicMargin s) hq
  have htwo : Equiv
      (BF4ExactSlabTwoProbeCovariance.covariance nome nome_pos nome_lt_one
        (L + thermodynamicMargin s) p q)
      (BF4ExactSlabTwoProbeCovariance.covariance nome nome_pos nome_lt_one
        (L + thermodynamicMargin s) ep eq) :=
    (CReal.sub_congr_left hpair).trans
      (CReal.sub_congr_right
        ((Pivot2.mul_congr_left hleft).trans
          (Pivot2.mul_congr_right hright)))
  exact (full_covariance_pin nome nome_pos nome_lt_one
      (L + thermodynamicMargin s) p q).trans
    (htwo.trans
      ((full_covariance_pin nome nome_pos nome_lt_one
        (L + thermodynamicMargin s) ep eq).symm.trans
        (lowerCovarianceSequence_faceSet
          (vectorJetLowerExpression L leftOffset hleftOffset)
          (vectorJetLowerExpression L rightOffset hrightOffset)
          (thermodynamicMargin s)).symm))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.thermodynamicPlacement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.baseLowerFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.baseLowerFaceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.baseLowerFaceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.baseLowerFaceId_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.shifted_vectorJetLowerExpression_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.thermodynamicPlacement_lowerFace_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.translatedLowerFacePlaced_expression_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement.thermodynamicPlacedFullCovariance_sequence_pin
