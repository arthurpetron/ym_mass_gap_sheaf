/-
# Canonical full-action endpoint for the exterior covariance tail

The selected-then-exterior action is a permutation of the canonical complete
physical target-face order.  Generic all-nome face-set permutation invariance
therefore turns the checked finite exterior telescope into a direct comparison
between the selected action and the canonical full target action, with the same
volume-uniform geometric tail.

This is still a fixed finite target slab and a finite heat-cutoff stage.  It
does not remove volume, construct the continuum theory or Hamiltonian, or prove
a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay (blockLength)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Physicality proof for the canonical translated selected action. -/
def zeroPlacementSelectedPhysical
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    ∀ id,
      id ∈ selectedIds (zeroPlacement s n L target hroom)
        (originalBulkVectorQuadraticJetIds s n L) →
      id ∈ slabPhysicalFaceEdges target :=
  selectedIds_physical (zeroPlacement s n L target hroom)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical_at_placement
      (zeroPlacement s n L target hroom) s n L rfl)

/-- Physicality proof for the selected-then-exterior complete action. -/
def zeroPlacementCompletedPhysical
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    ∀ id,
      id ∈
          selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L) ++
            zeroPlacementExteriorIds s n L target hroom →
      id ∈ slabPhysicalFaceEdges target := by
  intro id hid
  rcases List.mem_append.mp hid with hid | hid
  · exact zeroPlacementSelectedPhysical s n L target hroom id hid
  · exact zeroPlacementExteriorIds_physical s n L target hroom id hid

/-- Direct finite covariance comparison between the canonical full target
action and the translated selected action, with a target-volume-independent
exterior tail. -/
theorem finite_covariance_zeroPlacement_full_action_tail_bound
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
          (slabPhysicalFaceEdges target) (fun _ hid => hid)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n rightOffset rightFace) stage +
        -(finiteCovariance w hw0 hw1 target
          (selectedIds (zeroPlacement s n L target hroom)
            (originalBulkVectorQuadraticJetIds s n L))
          (zeroPlacementSelectedPhysical s n L target hroom)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (zeroPlacement s n L target hroom) n rightOffset rightFace) stage)) ≤
      coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace := by
  let P := zeroPlacement s n L target hroom
  let selected := selectedIds P (originalBulkVectorQuadraticJetIds s n L)
  let exterior := zeroPlacementExteriorIds s n L target hroom
  let completed := selected ++ exterior
  let leftObservable :=
    translatedOriginalBulkVectorQuadraticJetFacePlaced
      P n leftOffset leftFace
  let rightObservable :=
    translatedOriginalBulkVectorQuadraticJetFacePlaced
      P n rightOffset rightFace
  let selectedCovariance :=
    finiteCovariance w hw0 hw1 target selected
      (zeroPlacementSelectedPhysical s n L target hroom)
      leftObservable rightObservable stage
  let completedCovariance :=
    finiteCovariance w hw0 hw1 target completed
      (zeroPlacementCompletedPhysical s n L target hroom)
      leftObservable rightObservable stage
  let fullCovariance :=
    finiteCovariance w hw0 hw1 target (slabPhysicalFaceEdges target)
      (fun _ hid => hid) leftObservable rightObservable stage
  have hperm : completed.Perm (slabPhysicalFaceEdges target) := by
    simpa only [completed, selected, exterior, P] using
      zeroPlacement_selected_append_exterior_perm_full s n L target hroom
  have horder : Q'.eqv completedCovariance fullCovariance := by
    exact finiteCovariance_perm hw0 hw1 target completed
      (slabPhysicalFaceEdges target)
      (zeroPlacementCompletedPhysical s n L target hroom)
      (fun _ hid => hid) hperm leftObservable rightObservable stage
  have htail : Q'.abs (completedCovariance + -selectedCovariance) ≤
      coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace := by
    simpa only [completedCovariance, selectedCovariance, completed, selected,
      exterior, leftObservable, rightObservable, P] using
      finite_covariance_zeroPlacement_exterior_tail_bound
        hw0 hw1 hsmall hd hs s n leftOffset rightOffset L target hroom
        leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset stage
  have hpin : Q'.eqv
      (Q'.abs (fullCovariance + -selectedCovariance))
      (Q'.abs (completedCovariance + -selectedCovariance)) :=
    Q'.abs_eqv_congr
      (Q'.add_eqv_congr' (Q'.eqv_symm horder) (Q'.eqv_refl _))
  simpa only [fullCovariance, selectedCovariance, selected, leftObservable,
    rightObservable, P] using
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) htail

/-- The same canonical full-action comparison after removing the heat cutoff,
still at one fixed finite target slab.  The geometric exterior budget is
unchanged because the finite estimate is uniform in the cutoff stage. -/
theorem covariance_zeroPlacement_full_action_tail_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs
        (CReal.sub
          (covariance w hw0 hw1 target
            (slabPhysicalFaceEdges target) (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace))
          (covariance w hw0 hw1 target
            (selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L))
            (zeroPlacementSelectedPhysical s n L target hroom)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace))))
      (ofQ'
        (coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
          rightOffset L target hroom leftFace rightFace)) := by
  have hsum := convergesTo_abs (convergesTo_add
    (finite_covariance_converges w hw0 hw1 target
      (slabPhysicalFaceEdges target) (fun _ hid => hid)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        (zeroPlacement s n L target hroom) n leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        (zeroPlacement s n L target hroom) n rightOffset rightFace))
    (TrigAddCReal.convergesTo_neg
      (finite_covariance_converges w hw0 hw1 target
        (selectedIds (zeroPlacement s n L target hroom)
          (originalBulkVectorQuadraticJetIds s n L))
        (zeroPlacementSelectedPhysical s n L target hroom)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (zeroPlacement s n L target hroom) n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (zeroPlacement s n L target hroom) n rightOffset rightFace))))
  have hc : ConvergesTo
      (fun stage => ofQ' (Q'.abs
        (finiteCovariance w hw0 hw1 target
            (slabPhysicalFaceEdges target) (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace) stage +
          -(finiteCovariance w hw0 hw1 target
            (selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L))
            (zeroPlacementSelectedPhysical s n L target hroom)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace) stage))))
      (CReal.abs
        (CReal.sub
          (covariance w hw0 hw1 target
            (slabPhysicalFaceEdges target) (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace))
          (covariance w hw0 hw1 target
            (selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L))
            (zeroPlacementSelectedPhysical s n L target hroom)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace)))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ hsum
    intro stage
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc
    (convergesTo_const (ofQ'
      (coordinateExteriorCovarianceTailBudget hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace)))
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_covariance_zeroPlacement_full_action_tail_bound
      hw0 hw1 hsmall hd hs s n leftOffset rightOffset L target hroom
      leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))

/-- Direct fixed-volume cutoff-removed `epsilon` comparison with the canonical
full target action.  The sole new geometric premise is the explicit collar
inequality required by the computed exterior block cutoff. -/
theorem covariance_zeroPlacement_full_action_small
    {w epsilon : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
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
    leEv
      (CReal.abs
        (CReal.sub
          (covariance w hw0 hw1 target
            (slabPhysicalFaceEdges target) (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace))
          (covariance w hw0 hw1 target
            (selectedIds (zeroPlacement s n L target hroom)
              (originalBulkVectorQuadraticJetIds s n L))
            (zeroPlacementSelectedPhysical s n L target hroom)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (zeroPlacement s n L target hroom) n rightOffset rightFace))))
      (ofQ' epsilon) := by
  exact leEv_trans
    (covariance_zeroPlacement_full_action_tail_bound
      hw0 hw1 hsmall hd hs s n leftOffset rightOffset L target hroom
      leftFace rightFace hleftFace hrightFace hleftOffset hrightOffset)
    (leEv_of_le (ofQ'_le_ofQ'
      (coordinateExteriorCovarianceTailBudget_small hw0 hd hs s n
        leftOffset rightOffset L target hroom leftFace rightFace
        hleftFace hrightFace hleftOffset hrightOffset hepsilon hcollar)))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction.zeroPlacementSelectedPhysical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction.zeroPlacementCompletedPhysical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction.finite_covariance_zeroPlacement_full_action_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction.covariance_zeroPlacement_full_action_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorFullAction.covariance_zeroPlacement_full_action_small
