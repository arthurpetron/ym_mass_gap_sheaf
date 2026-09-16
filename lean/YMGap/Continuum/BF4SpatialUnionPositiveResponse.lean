/-
# Positive original response on the SAME completed spatial union

The old full-action numerator floor and the actual finite-action comparison
give responseFloor <= current covariance + a geometrically vanishing error.
A computed cutoff makes this error smaller than any supplied tolerance on
the original unchanged three-regulator diagonal. Its existing convergence
therefore preserves the FULL floor at physical lag three. Actual time
contraction then gives the same floor at lag two, with no one-step positivity
assumption and no interchange of regulator limits.

The existing original centered plaquette vector, completed pairing and time
are retained. This is fixed-spacing SU(2) at nome 1/1024, not continuum
nontriviality, a physical mass calibration, full QFT axioms or all-group closure.
-/

import YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison
import YMGap.Continuum.BF4SpatialUnionOddEvenResponse
import YMGap.Continuum.BF4SpatialUnionSmallNome
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4SpatialUnionPositiveResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionResponseProbePins
open YMGap.Continuum.BF4SpatialUnionResponseBoundary (depth)
open YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
  (spatialCenteredMoment originalConnected_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize boxAmplitude)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialComparison (rate_nonnegative)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionExcitation (excitation excitation_correlator_pin centralStage)
open YMGap.Continuum.BF4SpatialUnionCenteredForm (centeredMoment_diagonal_pin)
open YMGap.Continuum.BF4SpatialUnionOddEvenResponse (lagTwo_floor_of_lagThree)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "rho" => entropyRate 625 (adjustedCoreRate nome hd)
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "v" => excitation nome_pos nome_lt_one hsmall hd hs

/-- The existing original connected diagonal, with no rescheduled regulators. -/
def diagonal (r : Nat) : Q' :=
  connectedScalar nome_pos nome_lt_one (paddedWidth 1 r) r 3
    (recenter r centralProbe) (physicalTime 3 (recenter r centralProbe)) r

theorem amplitude_nonnegative : (0 : Q') ≤ errorAmplitude nome hd hs := by
  have hc : (0 : Q') ≤ singleCap := (currentUpper_interval 0).nonnegative
  unfold errorAmplitude
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 6) hc) hc)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (probePrefactor_nonnegative nome hd _)
        (ClusterCount.ofNat_nonneg _)) (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- Computes a sufficient ORIGINAL diagonal index for any positive tolerance. -/
def comparisonModulus (epsilon : Q') : Nat :=
  carrierSize 7 + geometricCutoff rho (errorAmplitude nome hd hs) epsilon + 1

theorem error_small (epsilon : Q') (he : (0 : Q') < epsilon) (r : Nat)
    (hr : comparisonModulus epsilon ≤ r) : errorBound nome hd hs (r-1) ≤ epsilon := by
  have hn : geometricCutoff rho (errorAmplitude nome hd hs) epsilon ≤ depth (r-1) := by
    unfold comparisonModulus depth at *
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (geometric_bound (rate_nonnegative nome_pos hd) hs amplitude_nonnegative he _ hn)

/-- The finite floor is eventually valid to every tolerance, with a computed index. -/
theorem diagonal_floor_error (epsilon : Q') (he : (0 : Q') < epsilon) (r : Nat)
    (hr : comparisonModulus epsilon ≤ r) : responseFloor ≤ diagonal r + epsilon := by
  have hr1 : 1 ≤ r := by unfold comparisonModulus at hr; omega
  have h := finite_lower_bound hsmall hd hs (r-1) r hr1
  have hp := diagonal_pin nome_pos nome_lt_one (r-1)
  change (diagonal ((r-1)+1)).eqv _ at hp
  rw [Nat.sub_add_cancel hr1] at hp
  exact Q'.le_trans' _ _ _ h
    (Q'.add_le_add (Q'.ge_of_eqv hp) (error_small epsilon he r hr))

theorem diagonal_converges :
    ConvergesTo (fun r => ofQ' (diagonal r))
      (spatialCenteredMoment nome_pos nome_lt_one 1 hsmall hd hs (by decide)
        3 centralProbe centralProbe) :=
  originalConnected_diagonal_converges nome_pos nome_lt_one 1 hsmall hd hs (by decide)
    3 3 centralProbe centralProbe (by decide) (by decide)

/-- The old full rational floor survives on the original spatial-limit scalar. -/
theorem spatial_response_floor :
    leEv (ofQ' responseFloor)
      (spatialCenteredMoment nome_pos nome_lt_one 1 hsmall hd hs (by decide)
        3 centralProbe centralProbe) :=
  leEv_of_ofQ'_limit_le (convergesTo_const _) diagonal_converges
    (fun epsilon he => ⟨comparisonModulus epsilon, diagonal_floor_error epsilon he⟩)

/-- SAME existing excitation and physical lag THREE, not the old completed carrier. -/
theorem lagThree_floor : RCle (Quotient.mk crealSetoid (ofQ' responseFloor)) (B v (T 3 v)) := by
  rw [excitation_correlator_pin]
  have hp := centeredMoment_diagonal_pin nome_pos nome_lt_one hsmall hd hs 3 centralStage
  exact leEv_trans spatial_response_floor (leEv_of_equiv hp.symm)

/-- Norm contraction compares lag three to lag two without assuming T_1 positive. -/
theorem lagTwo_floor : RCle (Quotient.mk crealSetoid (ofQ' responseFloor)) (B v (T 2 v)) :=
  lagTwo_floor_of_lagThree nome_pos nome_lt_one hsmall hd hs v _ lagThree_floor

/-- The constant and its proof are explicit data attached to the actual response. -/
def positiveResponse : Σ' c : Q', ((0 : Q') < c) ×'
    RCle (Quotient.mk crealSetoid (ofQ' c)) (B v (T 2 v)) :=
  ⟨responseFloor, responseFloor_positive, lagTwo_floor⟩

end YMGap.Continuum.BF4SpatialUnionPositiveResponse

#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.diagonal
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.comparisonModulus
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.error_small
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.diagonal_floor_error
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.diagonal_converges
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.spatial_response_floor
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.lagThree_floor
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.lagTwo_floor
#print axioms YMGap.Continuum.BF4SpatialUnionPositiveResponse.positiveResponse
