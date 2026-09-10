/-
# Extract the spatial anchor power from the two-scale terminal budget

The corridor theorem bounds each connected expanded witness by an anchor
power indexed by the complete fine/coarse peeling profile, multiplied by the
two accepted terminal weights and divided by the exact source-row
normalization.  The profile-mass floor proves that this exponent dominates
the observable-to-source separation.

This file performs the resulting exact factorization.  It leaves a single
nonnegative terminal residual

  fineTerminalWeight * coarseTerminalWeight / sourceNormalization

and places the spatial anchor power outside it.  Summing pointwise yields a
connected-mass bound by a distance-weighted terminal-residual mass.  Thus the
next inverse-fiber obligation is stated without an opaque prefactor and
without losing the source-dependent normalization.

Constructive contract: exact rational reassociation, exponent antitonicity,
and finite list induction only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem rgQpow_eqv_pow_local (value : Q') : ∀ exponent : Nat,
    qpow value exponent ≈ value ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      show qpow value exponent * value ≈ value * value ^ exponent
      exact Q'.eqv_trans _
        (value ^ exponent * value) _
        (Q'.mul_eqv_congr_right _ _ _
          (rgQpow_eqv_pow_local value exponent))
        (Q'.mul_comm_eqv _ _)

/-! ## 1. The terminal factor left after spatial payment -/

/-- Product of the fine and coarse accepted terminal weights, divided by the
exact normalization of the two physical source rows. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  Q'.divPos
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        result.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        result.2.1)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (0 : Q') ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded := by
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  let normalization := finePacketOrientedEnvelopeNormalizationMass S
    expanded.1.1.sources.1 expanded.1.1.sources.2
  have hnormalization : (0 : Q') < normalization :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ result.1.1)
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ result.2.1))
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))

/-! ## 2. Exact factorization and spatial weakening -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_power_mul_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded ≈
      anchorFaceCoefficient ^
          finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
            S rate hrate0 orientation observableFaceId hobservableFace expanded *
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace expanded := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
    Q'.divPos
  exact Q'.mul_assoc_eqv _ _ _

/-- Pure arithmetic contraction used by every compiled spatial certificate. -/
theorem anchorPower_mul_residual_le_distancePower_mul_residual
    (distance mass : Nat) (hdistance : distance ≤ mass)
    (residual : Q') (hresidual : (0 : Q') ≤ residual) :
    anchorFaceCoefficient ^ mass * residual ≤
      anchorFaceCoefficient ^ distance * residual := by
  have hpower := qpow_antitone
    (show (0 : Q') ≤ anchorFaceCoefficient by decide)
    (show anchorFaceCoefficient ≤ (1 : Q') by decide)
    distance mass hdistance
  have hpow' : anchorFaceCoefficient ^ mass ≤
      anchorFaceCoefficient ^ distance :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (rgQpow_eqv_pow_local anchorFaceCoefficient mass)))
      (Q'.le_trans' _ _ _ hpower
        (Q'.le_of_eqv
          (rgQpow_eqv_pow_local anchorFaceCoefficient distance)))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hpow' hresidual

/-- Small nondependent code on which the spatial contraction is performed. -/
structure FinePacketConnectedRateSpatialTerminalCode : Type where
  budget : Q'
  distance : Nat
  profileMass : Nat
  residual : Q'

def finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : FinePacketConnectedRateSpatialTerminalCode where
  budget :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded
  distance := finePacketGlobalNonzeroConnectedEntryDistance
    S orientation observableFaceId hobservableFace expanded.1
  profileMass :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  residual :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded

/-- Soundness of the compact spatial compiler.  Its budget is bounded by the
spatial power times the exact source-normalized terminal residual. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler_sound
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let code :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded
    code.budget ≤ anchorFaceCoefficient ^ code.distance * code.residual := by
  let code :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace expanded
  have hfactor : code.budget ≈
      anchorFaceCoefficient ^ code.profileMass * code.residual := by
    simpa only [code,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler]
      using
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_power_mul_residual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace expanded
  have hdistance : code.distance ≤ code.profileMass := by
    simpa only [code,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler]
      using
        finePacketGlobalNonzeroConnectedExpandedWitness_distance_le_rateTotalProfileMass
          S rate hrate0 orientation observableFaceId hobservableFace expanded
  have hresidual : (0 : Q') ≤ code.residual := by
    simpa only [code,
      finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler]
      using
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual_nonnegative
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace expanded
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (anchorPower_mul_residual_le_distancePower_mul_residual
      code.distance code.profileMass hdistance code.residual hresidual)

/-! ## 3. The aggregate connected residual frontier -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun expanded =>
      let code :=
        finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace expanded
      anchorFaceCoefficient ^ code.distance * code.residual)
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-- On the explicitly named SU(2) corridor, the complete connected witness
mass is bounded by the distance-weighted terminal residual.  No uniformity in
beta, lattice spacing, volume, or cutoff is asserted. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateDistanceTerminalResidualMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass
  apply listQSum_le_termwise_local
  intro expanded _
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace expanded)
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler_sound
      S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
        hobservableFace expanded)

#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget_eqv_power_mul_residual
#print axioms anchorPower_mul_residual_le_distancePower_mul_residual
#print axioms FinePacketConnectedRateSpatialTerminalCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateSpatialTerminalCompiler_sound
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateDistanceTerminalResidualMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateDistanceTerminalResidualMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
