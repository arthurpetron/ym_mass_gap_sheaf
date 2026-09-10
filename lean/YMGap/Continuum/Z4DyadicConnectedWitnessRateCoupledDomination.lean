/-
# Dominate a connected witness by its rate-coupled four-state weight

The flattened connected witness has two heat layers.  Its structural prefix
spends exactly the common fine-source/coarse-excitation heat exponent, while
its normalized joint witness retains the actual coarse parity-ground power.
The four accepted physical entries, rebased to a comparison rate, carry the
sum of precisely those two exponents.

This module proves both identifications and then uses the explicitly stated
comparison `S.coarse.coupling <= rate` to dominate the actual parity-ground
power.  Consequently every normalized connected witness is bounded by the
same exact normalization applied to its rate-coupled four-state weight.
There is no beta-uniform constant here: both the actual coupling and the
comparison range occur in the theorem statement.

Constructive contract: exact SU(2) Casimir identities, rational-power
monotonicity, and positive division only; no classical choice, proof hole,
trusted external computation, computability escape, heartbeat increase, or
new axiom.
-/

import YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
import YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeelingFaithfulness

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization
open YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem mul_rearrange_local (a b c d : Q') :
    (a * ((b * c) * d)) ≈ (a * (b * (d * c))) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem mul_div_rearrange_local (a b c reciprocal : Q') :
    a * ((b * reciprocal) * c) ≈ (a * (b * c)) * reciprocal := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem three_factor_regroup_local (a b c : Q') :
    a * (b * c) ≈ (a * b) * c := by
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a b c)

/-! ## 1. The structural prefix is the exact common heat power -/

theorem finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_eqv_commonPower
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
        S rate orientation observableFaceId hobservableFace entry ≈
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
          S orientation observableFaceId entry) := by
  let visible := qpow rate
    (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
      S orientation observableFaceId hobservableFace entry)
  let shape := qpow rate
    (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
      S orientation observableFaceId entry)
  let residual := qpow rate
    (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
      S orientation observableFaceId hobservableFace entry)
  let activity := qpow rate
    (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
      S orientation observableFaceId entry)
  let reserve := qpow rate
    (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
      S orientation observableFaceId entry)
  have hshape :=
    finePacketGlobalNonzeroConnectedEntryShapeChildWeight_eqv_heat
      rate S hfineCutoff orientation observableFaceId hobservableFace entry
  have hcomponent :=
    finePacketGlobalNonzeroConnectedEntry_componentHeatPower_eqv_rebalanced
      S hfineCutoff rate orientation observableFaceId hobservableFace entry
  have hexponent :=
    finePacketGlobalNonzeroConnectedEntry_componentHeat_add_reserve_eq_common
      S hfineCutoff orientation observableFaceId hobservableFace entry
  have hcommon :
      qpow rate
          (finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
            S orientation observableFaceId entry) ≈
        qpow rate
            (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
              S orientation observableFaceId entry) * reserve := by
    rw [← hexponent]
    exact YMGap.Continuum.HeatKernelRGStep.qpow_add rate _ _
  unfold finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
  refine Q'.eqv_trans _
    ((visible * ((shape * activity) * residual)) * reserve) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reserve
      (Q'.mul_eqv_congr_left visible _ _
        (Q'.mul_eqv_congr_right _ _ residual hshape))
  refine Q'.eqv_trans _
    ((visible * (shape * (residual * activity))) * reserve) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reserve
      (mul_rearrange_local visible shape activity residual)
  refine Q'.eqv_trans _
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
          S orientation observableFaceId entry) * reserve) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reserve (Q'.eqv_symm hcomponent)
  · exact Q'.eqv_symm hcommon

/-! ## 2. The four physical Casimirs split into common plus ground heat -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessCasimirExponent_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketOrientedJointUnitExpandedWitnessCasimirExponent
        S expanded.2.1 =
      finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
          S orientation observableFaceId expanded.1 +
        finePacketOrientedTotalTargetParityGroundCasimir
          S orientation expanded.1.1.sources.1.1
            expanded.1.1.sources.2.1 := by
  have hfineFirst :=
    finePacketOrientedJointUnitExpandedWitness_fineFirst_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hfineSecond :=
    finePacketOrientedJointUnitExpandedWitness_fineSecond_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hcoarseFirst :=
    finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hcoarseSecond :=
    finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hfineFirstCasimir :=
    slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
      S hfineCutoff expanded.1.1.sources.1.1
        expanded.1.1.sources.1.2.1
  have hfineSecondCasimir :=
    slabPhysicalCasimirExponent_eq_three_mul_occupiedFaceCount
      S hfineCutoff expanded.1.1.sources.2.1
        expanded.1.1.sources.2.2.1
  have hcoarseCasimir :=
    finePacketOrientedTargetCasimir_exact_decomposition
      S hfineCutoff orientation expanded.1.1.sources.1
        expanded.1.1.sources.2 expanded.1.1.targets
        (finePacketGlobalOrientedNonzeroConnectedEntryLowering
          S hfineCutoff orientation observableFaceId expanded.1)
  unfold finePacketOrientedJointUnitExpandedWitnessCasimirExponent
    slabAcceptedTwoReplicaStateCasimirExponent
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
    finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
    finePacketOrientedJointCommonRateExponent
  simp only [finePacketFineUnitCouplingSlabPhysicalData,
    coarseUnitCouplingSlabPhysicalData, SlabPhysicalData.extent]
  rw [hfineFirst, hfineSecond, hcoarseFirst, hcoarseSecond]
  change
    (slabPhysicalCasimirExponent S.fine.extent
          expanded.1.1.sources.1.1 +
        slabPhysicalCasimirExponent S.fine.extent
          expanded.1.1.sources.2.1) +
      (slabPhysicalCasimirExponent S.coarse.extent
          expanded.1.1.targets.1 +
        slabPhysicalCasimirExponent S.coarse.extent
          expanded.1.1.targets.2) = _
  rw [hfineFirstCasimir, hfineSecondCasimir, hcoarseCasimir]
  omega

/-! ## 3. Pointwise normalized domination by the rate-coupled weight -/

/-- The exact two-row normalization applied to the rate-coupled weight of
all four accepted entries. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  Q'.divPos
    (finePacketOrientedJointExpandedWitnessAtCouplingWeight
      S rate hrate0 expanded.2.1)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

private theorem finePacketOrientedJointUnitExpandedWitnessWeight_nonnegative
    (S : SlabScalePair)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) :
    (0 : Q') ≤ finePacketOrientedJointUnitExpandedWitnessWeight S witness := by
  have hfour : (0 : Q') ≤
      slabAcceptedTwoReplicaStateWeight
          (finePacketFineUnitCouplingSlabPhysicalData S) witness.1 *
        slabAcceptedTwoReplicaStateWeight
          (coarseUnitCouplingSlabPhysicalData S)
          (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
            S witness) :=
    Q'.mul_nonneg _ _
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ witness.1)
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ _)
  exact Q'.le_trans' _ _ _ hfour
    (Q'.ge_of_eqv
      (finePacketOrientedJointUnitExpandedWitnessWeight_eqv_fourState
        S witness))

/-- The actual coarse ground heat is the only inequality in the pointwise
comparison.  Its permitted coupling interval is explicit. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateCoupled
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId expanded := by
  let entry := expanded.1
  let witness := expanded.2.1
  let common := finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
    S orientation observableFaceId entry
  let ground := finePacketOrientedTotalTargetParityGroundCasimir
    S orientation entry.1.sources.1.1 entry.1.sources.2.1
  let unitWeight := finePacketOrientedJointUnitExpandedWitnessWeight S witness
  let normalization := finePacketOrientedEnvelopeNormalizationMass
    S entry.1.sources.1 entry.1.sources.2
  have hprefix :=
    finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_eqv_commonPower
      S hfineCutoff rate orientation observableFaceId hobservableFace entry
  have hgroundPower :=
    YMGap.Continuum.FusedAmplitudeDerivation.qpow_mono_base
      S.coarse.coupling_nonnegative hcoarseRate ground
  have hunit0 : (0 : Q') ≤ unitWeight :=
    finePacketOrientedJointUnitExpandedWitnessWeight_nonnegative S witness
  have hgroundScaled :
      qpow S.coarse.coupling ground * unitWeight ≤
        qpow rate ground * unitWeight :=
    Q'.mul_le_mul_of_nonneg_right _ _ unitWeight hgroundPower hunit0
  have hcommon0 : (0 : Q') ≤ qpow rate common :=
    qpow_nonneg rate hrate0 common
  have hnumeratorRaw :
      qpow rate common *
          (qpow S.coarse.coupling ground * unitWeight) ≤
        qpow rate common * (qpow rate ground * unitWeight) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgroundScaled hcommon0
  have htotalExponent :=
    finePacketGlobalNonzeroConnectedExpandedWitnessCasimirExponent_eq
      S hfineCutoff orientation observableFaceId expanded
  have hrateWeight :=
    finePacketOrientedJointExpandedWitnessAtCouplingWeight_eqv
      S rate hrate0 witness
  have hrightEqv :
      qpow rate common * (qpow rate ground * unitWeight) ≈
        finePacketOrientedJointExpandedWitnessAtCouplingWeight
          S rate hrate0 witness := by
    refine Q'.eqv_trans _
      ((qpow rate common * qpow rate ground) * unitWeight) _
      (three_factor_regroup_local _ _ _) ?_
    refine Q'.eqv_trans _
      (qpow rate (common + ground) * unitWeight) _
      (Q'.mul_eqv_congr_right _ _ unitWeight
        (Q'.eqv_symm
          (YMGap.Continuum.HeatKernelRGStep.qpow_add
            rate common ground))) ?_
    rw [← htotalExponent]
    exact Q'.eqv_symm hrateWeight
  have hnumerator :
      finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
          S rate orientation observableFaceId hobservableFace entry *
        (qpow S.coarse.coupling ground * unitWeight) ≤
      finePacketOrientedJointExpandedWitnessAtCouplingWeight
        S rate hrate0 witness := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ _ hprefix))
      (Q'.le_trans' _ _ _ hnumeratorRaw (Q'.le_of_eqv hrightEqv))
  have hnormalization : (0 : Q') < normalization :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        entry.1.sources.1 entry.1.sources.2
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos normalization hnormalization) hnumerator
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessWeight
    finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
    finePacketOrientedNormalizedJointExpandedWitnessWeight
    finePacketOrientedNormalizedJointExpandedWitnessScale
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
    Q'.divPos
  simpa only [entry, witness, common, ground, unitWeight, normalization] using
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (mul_div_rearrange_local
          (finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
            S rate orientation observableFaceId hobservableFace entry)
          (qpow S.coarse.coupling ground) unitWeight
          (Q'.recipPos normalization hnormalization)))
      hscaled)

#print axioms finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_eqv_commonPower
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessCasimirExponent_eq
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateCoupled

end YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination
