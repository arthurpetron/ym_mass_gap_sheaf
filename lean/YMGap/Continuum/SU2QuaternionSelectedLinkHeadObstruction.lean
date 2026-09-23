/-
# Existing-neighbor projection is not spectator-preserving head heat

The selected-link identification certificate quantifies over arbitrary
polynomials on both members of the selected pair.  Its proposed head-map
comparison instead introduces a fresh link and keeps the old neighbor as
a spectator.  These are different operations.  The two coordinate tests
below distinguish them on the actual finite Haar carrier.

This refutes a proposed local operator join, not Yang--Mills or the checked
BF4 completed-sector gap.  The original certificate statements are retained.
-/

import YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification

namespace YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFischerRadial
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

local infix:50 " ≈ " => Q'.eqv

def counterNome : Q' := Q'.mkPos 1 2 (by decide)
def counterState : RatPoly := polyVar 0
def counterTest : RatPoly := polyVar 4

theorem counterState_supported : SupportedQuaternionBlocks 2 counterState := by
  intro t ht
  simp only [counterState, polyVar, List.mem_singleton] at ht
  subst t
  decide

theorem counterTest_supported : SupportedQuaternionBlocks 2 counterTest := by
  intro t ht
  simp only [counterTest, polyVar, List.mem_singleton] at ht
  subst t
  decide

def counterRelativePairing : Q' :=
  quaternionHaar 2
    (polyMul
      (project 0
        (polyMul (relativeHeat counterNome 1)
          (exposeTranslationPairPolynomial 2 0 1 (by decide) (by decide)
            (by decide) counterState)))
      (exposeTranslationPairPolynomial 2 0 1 (by decide) (by decide)
        (by decide) counterTest))

def counterHeadPairing : Q' :=
  selectedLinkExposedHeatPair 1 0 1 (by decide) (by decide) (by decide)
    counterNome 1 counterState counterTest

/-- The actual existing-neighbor update transmits the coordinate. -/
theorem counterRelativePairing_value :
    counterRelativePairing ≈ Q'.mkPos 1 32 (by decide) := by decide

/-- The fresh-head heat pairing retains the old neighbor independently. -/
theorem counterHeadPairing_value : counterHeadPairing ≈ 0 := by decide

/-- The reduced certificate cannot be supplied even at this strict nome. -/
theorem selectedLinkExposedRelativePairing_uninhabited
    (input : SelectedLinkExposedRelativePairing
      1 0 1 (by decide) (by decide) (by decide) (by decide) counterNome 1) :
    False := by
  have h : counterRelativePairing ≈ counterHeadPairing :=
    input.pairing counterState counterTest counterState_supported counterTest_supported
  have hbad : Q'.mkPos 1 32 (by decide) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm counterRelativePairing_value)
      (Q'.eqv_trans _ _ _ h counterHeadPairing_value)
  exact (by decide : ¬ (Q'.mkPos 1 32 (by decide) ≈ (0 : Q'))) hbad

/-! The obstruction also occurs in the four-block geometry used by the
hybrid consumer (`n = 2`, selected pair `0,2`), at arbitrarily late cutoffs.
Padding is explicit so the existing harmonic-reproduction theorem applies. -/

def hybridCoordinate : RatPoly := [(1 :: List.replicate 15 0, 1)]

theorem hybridCoordinate_supported : SupportedQuaternionBlocks 4 hybridCoordinate := by
  intro t ht
  simp only [hybridCoordinate, List.mem_singleton] at ht
  subst t
  decide

theorem hybridCoordinate_project_zero :
    RatPolyCoeffEqv (project 0 hybridCoordinate) polyZero :=
  RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- Every output of this existing-neighbor update has cleared block zero;
its pairing with the centered block-zero coordinate is therefore zero. -/
theorem existingNeighbor_coordinate_pairing_zero (w : Q') (K : Nat) :
    quaternionHaar 4
      (polyMul
        (selectedHeatProjection 3 0 2 (by decide) (by decide) (by decide)
          w K hybridCoordinate) hybridCoordinate) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (project_selfAdjoint 4 0 (by decide) _ hybridCoordinate)
    (haar_of_coeff ((hybridCoordinate_project_zero.mul_left _).trans
      (RatPolyCoeffEqv.mul_zero_right _)))

theorem hybridCoordinate_norm :
    quaternionHaar 4 (polyMul hybridCoordinate hybridCoordinate) ≈
      Q'.mkPos 1 4 (by decide) := by decide

theorem hybridCoordinate_angular :
    quaternionHaar 4 (blockAngularSquare 0 hybridCoordinate) ≈
      Q'.mkPos 3 4 (by decide) := by decide

theorem hybridCoordinate_head_pairing (w : Q') (K : Nat) (hK : 1 ≤ K) :
    heatPair 3 w K hybridCoordinate hybridCoordinate ≈
      qpow w 3 * Q'.mkPos 1 4 (by decide) := by
  have hp : HeadPadded hybridCoordinate := by
    intro t ht
    simp only [hybridCoordinate, List.mem_singleton] at ht
    subst t
    decide
  have hd : HasQuaternionBlockDegree 0 1 hybridCoordinate := by
    intro t ht
    simp only [hybridCoordinate, List.mem_singleton] at ht
    subst t
    decide
  have hh : RatPolyCoeffEqv (headLaplacian hybridCoordinate) polyZero :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  have h := harmonic_pair 3 w K 1 hybridCoordinate hybridCoordinate
    hybridCoordinate_supported hp hd hh
  simp only [attenuation, if_pos hK] at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_left _ _ _ hybridCoordinate_norm)

theorem hybridCoordinate_conjugated_pairing (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 4
      (polyMul hybridCoordinate
        (chainConjugatedHeadMap
          (selectedPairSteps 3 0 2 (by decide) (by decide) (by decide))
          w K hybridCoordinate)) ≈
      qpow w 3 * Q'.mkPos 1 4 (by decide) := by
  have he : applyQuaternionBlockSwapChain
      (selectedPairSteps 3 0 2 (by decide) (by decide) (by decide))
      hybridCoordinate = hybridCoordinate := by decide
  have h := chainConjugatedHeadMap_pairing 3 w K
    (selectedPairSteps 3 0 2 (by decide) (by decide) (by decide))
    hybridCoordinate hybridCoordinate_supported
  rw [he] at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (headMap_pairing 3 w K _ _)
        (hybridCoordinate_head_pairing w K hK)))

/-- No later representation cutoff repairs the original identification,
including cutoffs satisfying the downstream angular-bound guard. -/
theorem hybrid_identification_uninhabited (K : Nat) (hK : 1 ≤ K)
    (input : SelectedLinkHeadIdentification
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K) :
    False := by
  have h := input.pairing hybridCoordinate hybridCoordinate
    hybridCoordinate_supported hybridCoordinate_supported
  have hbad : (0 : Q') ≈ Q'.mkPos 1 32 (by decide) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (existingNeighbor_coordinate_pairing_zero counterNome K))
      (Q'.eqv_trans _ _ _ h
        (Q'.eqv_trans _ _ _ (hybridCoordinate_conjugated_pairing counterNome K hK)
          (by decide)))
  exact (by decide : ¬ ((0 : Q') ≈ Q'.mkPos 1 32 (by decide))) hbad

theorem hybrid_exposedHeadPairing_uninhabited (K : Nat) (hK : 1 ≤ K)
    (input : SelectedLinkExposedHeadPairing
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K) :
    False :=
  hybrid_identification_uninhabited K hK
    (selectedLinkHeadIdentification_of_exposed
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K input)

theorem hybrid_relativePairing_uninhabited (K : Nat) (hK : 1 ≤ K)
    (input : SelectedLinkExposedRelativePairing
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K) :
    False :=
  hybrid_exposedHeadPairing_uninhabited K hK
    (selectedLinkExposedHeadPairing_of_relative
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K input)

theorem hybrid_projectionPairing_uninhabited (K : Nat) (hK : 1 ≤ K)
    (input : SelectedLinkExposedProjectionPairing
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K) :
    False :=
  hybrid_exposedHeadPairing_uninhabited K hK
    (selectedLinkExposedHeadPairing_of_projection
      3 0 2 (by decide) (by decide) (by decide) (by decide) counterNome K input)

/-- The counterexample meets the actual local consumer's computed cutoff
guard, not merely an unguarded low-cutoff specialization. -/
theorem hybrid_guardedRelativePairing_uninhabited
    (input : SelectedLinkExposedRelativePairing
      3 0 2 (by decide) (by decide) (by decide) (by decide)
      counterNome (sufficientCutoff counterNome)) : False :=
  hybrid_relativePairing_uninhabited _ (by decide) input

/-- The desired unconditioned local defect bound itself fails, for every
cutoff, at the strict nome 3/4.  This is not just a failure of a proof API. -/
theorem existingNeighbor_defect_bound_false (K : Nat) :
    ¬ (quaternionHaar 4 (polyMul hybridCoordinate hybridCoordinate) -
        quaternionHaar 4
          (polyMul hybridCoordinate
            (selectedHeatProjection 3 0 2 (by decide) (by decide) (by decide)
              (Q'.mkPos 3 4 (by decide)) K hybridCoordinate)) ≤
      ((1 : Q') - Q'.mkPos 3 4 (by decide)) *
        quaternionHaar 4 (blockAngularSquare 0 hybridCoordinate)) := by
  intro h
  have hzero := Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm hybridCoordinate _))
    (existingNeighbor_coordinate_pairing_zero (Q'.mkPos 3 4 (by decide)) K)
  have hl := Q'.add_eqv_congr' hybridCoordinate_norm (Q'.neg_eqv_congr _ _ hzero)
  have hr := Q'.mul_eqv_congr_left ((1 : Q') - Q'.mkPos 3 4 (by decide))
    _ _ hybridCoordinate_angular
  have hbad := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hl))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))
  exact (by decide : ¬ (Q'.mkPos 1 4 (by decide) - 0 ≤
    ((1 : Q') - Q'.mkPos 3 4 (by decide)) * Q'.mkPos 3 4 (by decide))) hbad

end YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction

#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.counterState_supported
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.counterTest_supported
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.counterRelativePairing_value
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.counterHeadPairing_value
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.selectedLinkExposedRelativePairing_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_supported
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_project_zero
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.existingNeighbor_coordinate_pairing_zero
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_norm
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_angular
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_head_pairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybridCoordinate_conjugated_pairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybrid_identification_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybrid_exposedHeadPairing_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybrid_relativePairing_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybrid_projectionPairing_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.hybrid_guardedRelativePairing_uninhabited
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadObstruction.existingNeighbor_defect_bound_false
