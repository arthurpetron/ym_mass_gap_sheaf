/-
# Full thermodynamic action versus the original selected lower-face law

The explicit thermodynamic placement has a canonical omitted-face complement.
Appending that complement to the translated selected action gives a
permutation of the complete physical target action, so the generic sequential
response telescope compares the literal full target covariance directly with
the translated selected covariance.  The latter is then pinned exactly to the
original unshifted selected source law.

The resulting bound is the finite structural sum of one-face insertion
budgets.  No geometric estimate for that sum, thermodynamic convergence of the
selected law, continuum limit, Hamiltonian gap, or Clay conclusion is proved
here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetPermutation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTelescope
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The translated selected vector-jet action in the thermodynamic target. -/
def thermodynamicSelectedIds (s L : Nat) : List Nat :=
  selectedIds (thermodynamicPlacement s L)
    (originalBulkVectorQuadraticJetIds s (s * s) L)

/-- Canonical complete-target order restricted to faces omitted by the
translated selected action. -/
def thermodynamicExteriorIds (s L : Nat) : List Nat :=
  (slabPhysicalFaceEdges (thermodynamicPlacement s L).target).filter fun id =>
    decide (id ∉ thermodynamicSelectedIds s L)

theorem thermodynamicSelectedIds_nodup (s L : Nat) :
    (thermodynamicSelectedIds s L).Nodup := by
  unfold thermodynamicSelectedIds selectedIds
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    (thermodynamicPlacement s L).faceId
    (originalBulkVectorQuadraticJetIds s (s * s) L)
  · unfold originalBulkVectorQuadraticJetIds
      SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainderIds
    exact chainIds_nodup _ _ _ _
  · intro left hleft right hright heq
    exact (thermodynamicPlacement s L).faceId_injective
      (originalBulkVectorQuadraticJetIds_physical s (s * s) L left hleft)
      (originalBulkVectorQuadraticJetIds_physical s (s * s) L right hright)
      heq

theorem thermodynamicExteriorIds_mem_iff (s L id : Nat) :
    id ∈ thermodynamicExteriorIds s L ↔
      id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target ∧
        id ∉ thermodynamicSelectedIds s L := by
  simp [thermodynamicExteriorIds]

theorem thermodynamicExteriorIds_physical (s L : Nat) :
    ∀ id, id ∈ thermodynamicExteriorIds s L →
      id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target := by
  intro id hid
  exact (thermodynamicExteriorIds_mem_iff s L id).mp hid |>.1

theorem thermodynamicExteriorIds_omitted (s L : Nat) :
    ∀ id, id ∈ thermodynamicExteriorIds s L →
      id ∉ thermodynamicSelectedIds s L := by
  intro id hid
  exact (thermodynamicExteriorIds_mem_iff s L id).mp hid |>.2

theorem thermodynamicExteriorIds_nodup (s L : Nat) :
    (thermodynamicExteriorIds s L).Nodup := by
  unfold thermodynamicExteriorIds slabPhysicalFaceEdges
  exact List.filter_sublist.nodup
    (YMGap.Continuum.CayleyParentInj.range_nodup _)

/-- Physicality proof for the translated selected thermodynamic action. -/
def thermodynamicSelectedPhysical (s L : Nat) :
    ∀ id, id ∈ thermodynamicSelectedIds s L →
      id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target := by
  intro id hid
  apply selectedIds_physical (thermodynamicPlacement s L)
    (originalBulkVectorQuadraticJetIds s (s * s) L)
    (originalBulkVectorQuadraticJetIds_physical_at_placement
      (thermodynamicPlacement s L) s (s * s) L rfl)
  exact hid

/-- Physicality proof for the selected-then-exterior complete action. -/
def thermodynamicCompletedPhysical (s L : Nat) :
    ∀ id,
      id ∈ thermodynamicSelectedIds s L ++ thermodynamicExteriorIds s L →
        id ∈ slabPhysicalFaceEdges (thermodynamicPlacement s L).target := by
  intro id hid
  rcases List.mem_append.mp hid with hselected | hexterior
  · exact thermodynamicSelectedPhysical s L id hselected
  · exact thermodynamicExteriorIds_physical s L id hexterior

theorem thermodynamic_selected_append_exterior_nodup (s L : Nat) :
    (thermodynamicSelectedIds s L ++ thermodynamicExteriorIds s L).Nodup := by
  refine List.nodup_append.mpr
    ⟨thermodynamicSelectedIds_nodup s L,
      thermodynamicExteriorIds_nodup s L, ?_⟩
  intro selected hselected omitted homitted heq
  subst omitted
  exact (thermodynamicExteriorIds_omitted s L selected homitted) hselected

/-- The selected action followed by its canonical complement is a complete
physical target action order. -/
theorem thermodynamic_selected_append_exterior_perm_full (s L : Nat) :
    (thermodynamicSelectedIds s L ++ thermodynamicExteriorIds s L).Perm
      (slabPhysicalFaceEdges (thermodynamicPlacement s L).target) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · exact thermodynamic_selected_append_exterior_nodup s L
  · unfold slabPhysicalFaceEdges
    exact YMGap.Continuum.CayleyParentInj.range_nodup _
  · intro id
    constructor
    · intro hid
      exact thermodynamicCompletedPhysical s L id hid
    · intro hphysical
      by_cases hselected : id ∈ thermodynamicSelectedIds s L
      · exact List.mem_append.mpr (Or.inl hselected)
      · exact List.mem_append.mpr (Or.inr
          ((thermodynamicExteriorIds_mem_iff s L id).mpr
            ⟨hphysical, hselected⟩))

/-- Structural sum of one-face response budgets for the thermodynamic
complement. -/
def thermodynamicExteriorCovarianceBudget
    {w : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) : Q' :=
  listQSum
    (coordinateCovarianceInsertionBudget hd hs
      (thermodynamicPlacement s L) (s * s) leftOffset rightOffset
      leftFace rightFace)
    (thermodynamicExteriorIds s L)

/-- The arbitrary-placement insertion theorem specialized to the complete
thermodynamic complement. -/
theorem finite_covariance_thermodynamic_exterior_telescope
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (stage : Nat) :
    Q'.abs
      (finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
          (thermodynamicSelectedIds s L ++ thermodynamicExteriorIds s L)
          (thermodynamicCompletedPhysical s L)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
          stage +
        -(finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
          (thermodynamicSelectedIds s L)
          (thermodynamicSelectedPhysical s L)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
          stage)) ≤
      thermodynamicExteriorCovarianceBudget hd hs s L leftOffset rightOffset
        leftFace rightFace := by
  simpa only [thermodynamicSelectedIds, thermodynamicExteriorCovarianceBudget,
    thermodynamicSelectedPhysical, thermodynamicCompletedPhysical] using
    (finite_covariance_append_bound_translatedFacePairCoordinateCarrier
      (thermodynamicPlacement s L) hw0 hw1 hsmall hd hs
      s (s * s) leftOffset rightOffset L leftFace rightFace rfl
      hleftFace hrightFace hleftOffset hrightOffset
      (thermodynamicSelectedIds s L) (thermodynamicExteriorIds s L)
      (thermodynamic_selected_append_exterior_nodup s L)
      (thermodynamicSelectedPhysical s L)
      (thermodynamicExteriorIds_physical s L) stage)

/-- Permutation invariance identifies the completed telescope endpoint with
the canonical complete physical target action. -/
theorem finite_covariance_thermodynamic_full_action_structural_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (stage : Nat) :
    Q'.abs
      (finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
          (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
          (fun _ hid => hid)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
          stage +
        -(finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
          (thermodynamicSelectedIds s L)
          (thermodynamicSelectedPhysical s L)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
          stage)) ≤
      thermodynamicExteriorCovarianceBudget hd hs s L leftOffset rightOffset
        leftFace rightFace := by
  let completed := thermodynamicSelectedIds s L ++ thermodynamicExteriorIds s L
  let leftObservable := translatedOriginalBulkVectorQuadraticJetFacePlaced
    (thermodynamicPlacement s L) (s * s) leftOffset leftFace
  let rightObservable := translatedOriginalBulkVectorQuadraticJetFacePlaced
    (thermodynamicPlacement s L) (s * s) rightOffset rightFace
  let selectedCovariance := finiteCovariance w hw0 hw1
    (thermodynamicPlacement s L).target (thermodynamicSelectedIds s L)
    (thermodynamicSelectedPhysical s L) leftObservable rightObservable stage
  let completedCovariance := finiteCovariance w hw0 hw1
    (thermodynamicPlacement s L).target completed
    (thermodynamicCompletedPhysical s L) leftObservable rightObservable stage
  let fullCovariance := finiteCovariance w hw0 hw1
    (thermodynamicPlacement s L).target
    (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
    (fun _ hid => hid) leftObservable rightObservable stage
  have horder : Q'.eqv completedCovariance fullCovariance := by
    exact finiteCovariance_perm hw0 hw1 (thermodynamicPlacement s L).target
      completed (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
      (thermodynamicCompletedPhysical s L) (fun _ hid => hid)
      (thermodynamic_selected_append_exterior_perm_full s L)
      leftObservable rightObservable stage
  have htail : Q'.abs (completedCovariance + -selectedCovariance) ≤
      thermodynamicExteriorCovarianceBudget hd hs s L leftOffset rightOffset
        leftFace rightFace := by
    simpa only [completedCovariance, selectedCovariance, completed,
      leftObservable, rightObservable] using
      (finite_covariance_thermodynamic_exterior_telescope
        hw0 hw1 hsmall hd hs s L leftOffset rightOffset leftFace rightFace
        hleftFace hrightFace hleftOffset hrightOffset stage)
  have hpin : Q'.eqv
      (Q'.abs (fullCovariance + -selectedCovariance))
      (Q'.abs (completedCovariance + -selectedCovariance)) :=
    Q'.abs_eqv_congr
      (Q'.add_eqv_congr' (Q'.eqv_symm horder) (Q'.eqv_refl _))
  simpa only [fullCovariance, selectedCovariance, leftObservable,
    rightObservable] using
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) htail

/-- The same structural full-versus-selected bound after removing the heat
cutoff at the fixed thermodynamic target. -/
theorem covariance_thermodynamic_full_action_structural_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs
        (CReal.sub
          (covariance w hw0 hw1 (thermodynamicPlacement s L).target
            (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
            (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace))
          (covariance w hw0 hw1 (thermodynamicPlacement s L).target
            (thermodynamicSelectedIds s L)
            (thermodynamicSelectedPhysical s L)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace))))
      (ofQ' (thermodynamicExteriorCovarianceBudget hd hs s L leftOffset
        rightOffset leftFace rightFace)) := by
  have hsum := convergesTo_abs (convergesTo_add
    (finite_covariance_converges w hw0 hw1 (thermodynamicPlacement s L).target
      (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
      (fun _ hid => hid)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
      (translatedOriginalBulkVectorQuadraticJetFacePlaced
        (thermodynamicPlacement s L) (s * s) rightOffset rightFace))
    (TrigAddCReal.convergesTo_neg
      (finite_covariance_converges w hw0 hw1
        (thermodynamicPlacement s L).target (thermodynamicSelectedIds s L)
        (thermodynamicSelectedPhysical s L)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (thermodynamicPlacement s L) (s * s) rightOffset rightFace))))
  have hc : ConvergesTo
      (fun stage => ofQ' (Q'.abs
        (finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
            (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
            (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
            stage +
          -(finiteCovariance w hw0 hw1 (thermodynamicPlacement s L).target
            (thermodynamicSelectedIds s L)
            (thermodynamicSelectedPhysical s L)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace)
            stage))))
      (CReal.abs
        (CReal.sub
          (covariance w hw0 hw1 (thermodynamicPlacement s L).target
            (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
            (fun _ hid => hid)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace))
          (covariance w hw0 hw1 (thermodynamicPlacement s L).target
            (thermodynamicSelectedIds s L)
            (thermodynamicSelectedPhysical s L)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
            (translatedOriginalBulkVectorQuadraticJetFacePlaced
              (thermodynamicPlacement s L) (s * s) rightOffset rightFace)))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ hsum
    intro stage
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc
    (convergesTo_const (ofQ'
      (thermodynamicExteriorCovarianceBudget hd hs s L leftOffset
        rightOffset leftFace rightFace)))
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_covariance_thermodynamic_full_action_structural_bound
      hw0 hw1 hsmall hd hs s L leftOffset rightOffset leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon))

/-- The translated selected thermodynamic endpoint is exactly the original
unshifted selected source covariance. -/
theorem thermodynamic_selected_covariance_source_pin
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    Equiv
      (covariance w hw0 hw1 (thermodynamicPlacement s L).target
        (thermodynamicSelectedIds s L)
        (thermodynamicSelectedPhysical s L)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          (thermodynamicPlacement s L) (s * s) rightOffset rightFace))
      (originalSelectedFacePairCovariance hw0 hw1 s (s * s) L leftOffset
        rightOffset leftFace rightFace) := by
  simpa only [thermodynamicSelectedIds, thermodynamicSelectedPhysical,
    originalSelectedFacePairCovariance] using
    (covariance_translatedFacePair_pin
      (thermodynamicPlacement s L) hw0 hw1 s (s * s) L leftOffset
      rightOffset rfl hleftOffset hrightOffset leftFace rightFace
      hleftFace hrightFace)

/-- Direct fixed-target comparison between the literal complete
thermodynamic action and the original selected source law. -/
theorem thermodynamic_full_action_source_structural_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs (CReal.sub
        (covariance w hw0 hw1 (thermodynamicPlacement s L).target
          (slabPhysicalFaceEdges (thermodynamicPlacement s L).target)
          (fun _ hid => hid)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) leftOffset leftFace)
          (translatedOriginalBulkVectorQuadraticJetFacePlaced
            (thermodynamicPlacement s L) (s * s) rightOffset rightFace))
        (originalSelectedFacePairCovariance hw0 hw1 s (s * s) L leftOffset
          rightOffset leftFace rightFace)))
      (ofQ' (thermodynamicExteriorCovarianceBudget hd hs s L leftOffset
        rightOffset leftFace rightFace)) := by
  have hpin := thermodynamic_selected_covariance_source_pin hw0 hw1 s L
    leftOffset rightOffset leftFace rightFace hleftFace hrightFace
    hleftOffset hrightOffset
  exact leEv_trans
    (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right hpin.symm)))
    (covariance_thermodynamic_full_action_structural_bound
      hw0 hw1 hsmall hd hs s L leftOffset rightOffset leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset)

private theorem nomeSmall : heatRatio nome ≤ HalfPow.half :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1

private theorem nomeDelta : heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2

private theorem nomeEntropy :
    entropyRate 625 (adjustedCoreRate nome nomeDelta) < 1 :=
  BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2

/-- The actual scheduled lower-face source covariance before thermodynamic
placement. -/
def thermodynamicOriginalSelectedLowerCovariance
    (s L leftOffset rightOffset : Nat) : CReal :=
  originalSelectedFacePairCovariance nome_pos nome_lt_one s (s * s) L
    leftOffset rightOffset (bulkSourceLowerFace s) (bulkSourceLowerFace s)

/-- At the fixed pilot nome, the exact full thermodynamic covariance and the
actual original selected lower-face covariance differ by only the displayed
finite structural exterior sum. -/
theorem thermodynamicPlacedFullCovariance_source_structural_bound
    (s L leftOffset rightOffset : Nat) (hside : 0 < s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs (CReal.sub
        (thermodynamicPlacedFullCovariance s L leftOffset rightOffset)
        (thermodynamicOriginalSelectedLowerCovariance
          s L leftOffset rightOffset)))
      (ofQ' (thermodynamicExteriorCovarianceBudget nomeDelta nomeEntropy
        s L leftOffset rightOffset (bulkSourceLowerFace s)
        (bulkSourceLowerFace s))) := by
  simpa only [thermodynamicPlacedFullCovariance,
    thermodynamicOriginalSelectedLowerCovariance,
    thermodynamicPlacement_target] using
    (thermodynamic_full_action_source_structural_bound
      nome_pos nome_lt_one nomeSmall nomeDelta nomeEntropy s L leftOffset
      rightOffset (bulkSourceLowerFace s) (bulkSourceLowerFace s)
      (bulkSourceLowerFace_mem s hside) (bulkSourceLowerFace_mem s hside)
      hleftOffset hrightOffset)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.thermodynamicSelectedIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.thermodynamic_selected_append_exterior_perm_full
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.finite_covariance_thermodynamic_exterior_telescope
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.covariance_thermodynamic_full_action_structural_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.thermodynamic_selected_covariance_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.thermodynamic_full_action_source_structural_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction.thermodynamicPlacedFullCovariance_source_structural_bound
