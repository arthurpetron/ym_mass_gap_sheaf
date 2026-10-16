/-
# Sequential exterior-face covariance telescope

The explicit one-face coordinate-carrier response is iterated over an arbitrary
duplicate-free list of additional physical action faces.  The resulting finite
covariance difference is bounded by the structural sum of the same one-face
budgets, with no dependence of a budget on the preceding insertion prefix.

Specializing the base list to the zero-placement selected action and the added
list to its canonical omitted complement gives the finite selected-to-complete-
order telescope needed by the exterior-margin estimate.  This module does not
yet identify the permuted complete order with the canonical full-action law,
bound the budget sum geometrically, remove either cutoff or volume, construct a
continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabGuardedCovarianceResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateGuardedResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem appendPhysicalList {extent : Nat} {base extra : List Nat}
    (hbase : ∀ id, id ∈ base → id ∈ slabPhysicalFaceEdges extent)
    (hextra : ∀ id, id ∈ extra → id ∈ slabPhysicalFaceEdges extent) :
    ∀ id, id ∈ base ++ extra → id ∈ slabPhysicalFaceEdges extent := by
  intro id hid
  rcases List.mem_append.mp hid with hid | hid
  · exact hbase id hid
  · exact hextra id hid

private theorem appendPhysicalOne {extent : Nat} {base : List Nat} {id : Nat}
    (hbase : ∀ j, j ∈ base → j ∈ slabPhysicalFaceEdges extent)
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    ∀ j, j ∈ base ++ [id] → j ∈ slabPhysicalFaceEdges extent := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact hbase j hj
  · rw [List.mem_singleton.mp hj]
    exact hid

private theorem addSubLeftCancelEqv (base extra : Q') :
    (base + extra) + -base ≈ extra := by
  refine Q'.eqv_trans _ (base + (extra + -base)) _
    (Q'.add_assoc_eqv base extra (-base)) ?_
  refine Q'.eqv_trans _ (base + (-base + extra)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl base)
      (Q'.add_comm_eqv extra (-base))) ?_
  refine Q'.eqv_trans _ ((base + -base) + extra) _
    (Q'.eqv_symm (Q'.add_assoc_eqv base (-base) extra)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + extra) _
    (Q'.add_eqv_congr' (Q'.add_neg_self_eqv base)
      (Q'.eqv_refl extra)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' extra)

private theorem covarianceTelescopeForwardEqv
    (initial middle terminal : Q') :
    (middle + -initial) + (terminal + -middle) ≈
      terminal + -initial := by
  refine Q'.eqv_trans _
    (((middle + -initial) + terminal) + -middle) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (middle + -initial) terminal (-middle))) ?_
  refine Q'.eqv_trans _
    ((middle + (terminal + -initial)) + -middle) _ ?_ ?_
  · apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (middle + (-initial + terminal)) _
        (Q'.add_assoc_eqv middle (-initial) terminal) ?_
      exact Q'.add_eqv_congr' (Q'.eqv_refl middle)
        (Q'.add_comm_eqv (-initial) terminal)
    · exact Q'.eqv_refl _
  · exact addSubLeftCancelEqv middle (terminal + -initial)

private theorem covarianceTelescopeEqv (initial middle terminal : Q') :
    (terminal + -initial) ≈
      (middle + -initial) + (terminal + -middle) :=
  Q'.eqv_symm (covarianceTelescopeForwardEqv initial middle terminal)

private theorem absAddNegSelfLeZero (value : Q') :
    Q'.abs (value + -value) ≤ 0 := by
  refine Q'.le_trans' _ (Q'.abs 0) _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.add_neg_self_eqv value))) ?_
  exact Q'.abs_le (by decide) (by decide)

/-- The fixed one-face budget used at every prefix of the exterior telescope. -/
def coordinateCovarianceInsertionBudget
    {w : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (P : Placement) (n leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) (id : Nat) : Q' :=
  covarianceBudget hd hs
    (translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      P n leftOffset rightOffset leftFace rightFace)
    (slabPlaquetteAt P.target id)
    (translatedOriginalBulkVectorQuadraticJetFacePairCap
      n leftOffset rightOffset leftFace rightFace)

/-- Sequential finite covariance response for an arbitrary physical extension
of a duplicate-free base action. -/
theorem finite_covariance_append_bound_translatedFacePairCoordinateCarrier
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L : Nat)
    (leftFace rightFace : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (base extra : List Nat) (hnodup : (base ++ extra).Nodup)
    (hbase : ∀ id, id ∈ base → id ∈ slabPhysicalFaceEdges P.target)
    (hextra : ∀ id, id ∈ extra → id ∈ slabPhysicalFaceEdges P.target)
    (stage : Nat) :
    Q'.abs
      (finiteCovariance w hw0 hw1 P.target (base ++ extra)
          (appendPhysicalList hbase hextra)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace) stage +
        -(finiteCovariance w hw0 hw1 P.target base hbase
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            P n rightOffset rightFace) stage)) ≤
      listQSum
        (coordinateCovarianceInsertionBudget hd hs P n leftOffset rightOffset
          leftFace rightFace) extra := by
  induction extra generalizing base with
  | nil =>
      simpa only [List.append_nil, listQSum] using
        absAddNegSelfLeZero
          (finiteCovariance w hw0 hw1 P.target base hbase
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              P n leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              P n rightOffset rightFace) stage)
  | cons id tail ih =>
      have hid : id ∈ slabPhysicalFaceEdges P.target :=
        hextra id List.mem_cons_self
      have htail : ∀ j, j ∈ tail → j ∈ slabPhysicalFaceEdges P.target := by
        intro j hj
        exact hextra j (List.mem_cons_of_mem id hj)
      have hnodup' : ((base ++ [id]) ++ tail).Nodup := by
        simpa only [List.singleton_append, List.append_assoc] using hnodup
      have hbaseOneNodup : (base ++ [id]).Nodup :=
        (List.nodup_append.mp hnodup').1
      have hbaseNodup : base.Nodup :=
        (List.nodup_append.mp hbaseOneNodup).1
      have hstep :=
        finite_covariance_insertion_bound_translatedFacePairCoordinateCarrier
          P hw0 hw1 hsmall hd hs s n leftOffset rightOffset L
          leftFace rightFace hsource hleftFace hrightFace
          hleftOffset hrightOffset base hbaseNodup hbase id hid stage
      have htailBound := ih (base := base ++ [id]) hnodup'
        (appendPhysicalOne hbase hid) htail
      let initial := finiteCovariance w hw0 hw1 P.target base hbase
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n rightOffset rightFace) stage
      let middle := finiteCovariance w hw0 hw1 P.target (base ++ [id])
        (appendPhysicalOne hbase hid)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n rightOffset rightFace) stage
      let terminal := finiteCovariance w hw0 hw1 P.target
        ((base ++ [id]) ++ tail)
        (appendPhysicalList (appendPhysicalOne hbase hid) htail)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n rightOffset rightFace) stage
      have htelescope :
          Q'.abs (terminal + -initial) ≤
            Q'.abs (middle + -initial) + Q'.abs (terminal + -middle) := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.abs_eqv_congr
              (covarianceTelescopeEqv initial middle terminal))) ?_
        exact Q'.abs_add_le' (middle + -initial) (terminal + -middle)
      have hstep' : Q'.abs (middle + -initial) ≤
          coordinateCovarianceInsertionBudget hd hs P n leftOffset rightOffset
            leftFace rightFace id := by
        simpa only [initial, middle, coordinateCovarianceInsertionBudget] using hstep
      have htailBound' : Q'.abs (terminal + -middle) ≤
          listQSum
            (coordinateCovarianceInsertionBudget hd hs P n leftOffset rightOffset
              leftFace rightFace) tail := by
        simpa only [middle, terminal, List.append_assoc,
          List.singleton_append] using htailBound
      have htotal := Q'.le_trans' _ _ _ htelescope
        (Q'.add_le_add hstep' htailBound')
      simpa only [initial, terminal, listQSum, List.append_assoc,
        List.singleton_append] using htotal

/-- The canonical zero-placement selected action extended by every omitted
physical target face, in the explicit selected-then-exterior order. -/
theorem finite_covariance_zeroPlacement_exterior_telescope
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
      listQSum
        (coordinateCovarianceInsertionBudget hd hs
          (zeroPlacement s n L target hroom) n leftOffset rightOffset
          leftFace rightFace)
        (zeroPlacementExteriorIds s n L target hroom) := by
  exact finite_covariance_append_bound_translatedFacePairCoordinateCarrier
    (zeroPlacement s n L target hroom) hw0 hw1 hsmall hd hs
    s n leftOffset rightOffset L leftFace rightFace rfl
    hleftFace hrightFace hleftOffset hrightOffset
    (selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L))
    (zeroPlacementExteriorIds s n L target hroom)
    (zeroPlacement_selected_append_exterior_nodup s n L target hroom)
    (selectedIds_physical (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L)
      (originalBulkVectorQuadraticJetIds_physical_at_placement
        (zeroPlacement s n L target hroom) s n L rfl))
    (zeroPlacementExteriorIds_physical s n L target hroom) stage

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope.coordinateCovarianceInsertionBudget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope.finite_covariance_append_bound_translatedFacePairCoordinateCarrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope.finite_covariance_zeroPlacement_exterior_telescope
