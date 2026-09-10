/-
# Rewrite terminal history mass as explicit posterior mass

The selected terminal-row residual has now been factored into an exact
oriented SU(2) lowering multiplicity and a beta-dependent terminal posterior.
This module substitutes that identity into the complete two-rate row sum.
It proves that the existing normalized-history upper bound is exactly the
finite posterior mass

  spatialRate^distance *
    historyRate^profileMass *
    loweringMultiplicity * terminalPosterior.

Thus the next mathematical obligation is no longer an injective code for bare
histories.  It is a weighted posterior normalization estimate, with every
coupling parameter and every finite multiplicity still visible.

Constructive contract: finite search, exact finite sums, and rational setoid
algebra only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorFactorization
import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorMass

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorFactorization
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateSplit

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit posterior summand -/

/-- The history part of one row after exposing both the exact lowering
multiplicity and the source-normalized terminal posterior. -/
def finePacketConnectedRateTerminalSkeletonHistoryPosteriorWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (historyRate : Q')
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  historyRate ^
      finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row *
    (Q'.ofNat
        (finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row) *
      finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row)

/-- The full two-rate posterior summand. -/
def finePacketConnectedRateTerminalSkeletonTwoRatePosteriorWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  spatialRate ^
      (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row) *
    finePacketConnectedRateTerminalSkeletonHistoryPosteriorWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace historyRate row

/-- Every realized old two-rate summand is exactly its explicit posterior
form. -/
theorem finePacketConnectedRateTerminalSkeletonTwoRateWeight_eqv_posteriorWeight_of_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q')
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    finePacketConnectedRateTerminalSkeletonTwoRateWeight
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate row ≈
      finePacketConnectedRateTerminalSkeletonTwoRatePosteriorWeight
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate row := by
  obtain ⟨structural, hfirst, hstructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hstructuralCarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  obtain ⟨reference, hreference, _hreferenceMem, _hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructuralCarrier
  have hfactor :=
    finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eqv_loweringMultiplicity_mul_terminalPosterior_of_selected
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hfirst reference hreference
  unfold finePacketConnectedRateTerminalSkeletonTwoRateWeight
    finePacketConnectedRateTerminalSkeletonTwoRatePosteriorWeight
    finePacketConnectedRateTerminalSkeletonHistoryPosteriorWeight
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hfactor)

/-! ## 2. Exact total posterior rewrite -/

def finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') : Q' :=
  listQSum
    (finePacketConnectedRateTerminalSkeletonTwoRatePosteriorWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace spatialRate historyRate)
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_posteriorMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') :
    finePacketConnectedRateTerminalSkeletonTwoRateMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate ≈
      finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate := by
  unfold finePacketConnectedRateTerminalSkeletonTwoRateMass
    finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
  apply listQSum_congr_on
  intro row hrow
  exact
    finePacketConnectedRateTerminalSkeletonTwoRateWeight_eqv_posteriorWeight_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace spatialRate historyRate row hrow

/-- The normalization-code presentation and the posterior-row presentation
are two exact finite reindexings of the same two-rate mass. -/
theorem finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass_eqv_posteriorMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (spatialRate historyRate : Q') :
    finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate ≈
      finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_normalizationMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace spatialRate historyRate))
    (finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_posteriorMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace spatialRate historyRate)

/-! ## 3. Repoint the proved corridor bound -/

/-- On the explicit SU(2) strong-coupling corridor, the connected expanded
witness mass is bounded by the concrete posterior mass with spatial rate
`4/5` and history rate `2/5`.  The next frontier is to normalize this weighted
posterior mass, not to count its histories uniformly. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsPosteriorMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 4 5 (by decide))
            (Q'.mkPos 2 5 (by decide)) := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  have hbound :=
    finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsNormalizedHistoryMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        hrateAnchor orientation observableFaceId hobservableFace
  have hreindex :=
    finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass_eqv_posteriorMass
      S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
        hobservableFace (Q'.mkPos 4 5 (by decide))
          (Q'.mkPos 2 5 (by decide))
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hreindex)

#print axioms finePacketConnectedRateTerminalSkeletonHistoryPosteriorWeight
#print axioms finePacketConnectedRateTerminalSkeletonTwoRatePosteriorWeight
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateWeight_eqv_posteriorWeight_of_mem
#print axioms finePacketConnectedRateTerminalSkeletonTwoRatePosteriorMass
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateMass_eqv_posteriorMass
#print axioms finePacketConnectedRateTerminalSkeletonTwoRateNormalizationMass_eqv_posteriorMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateFourFifthsDistanceTwoFifthsPosteriorMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorMass
