/-
# Exact component heat budget on the nonzero connected carrier

Every surviving oriented entry has a genuine lowering pair and a canonical
observable-rooted target-support component.  The joint activity on that
component pays the geometric separation.  Three times the component
activity is, in turn, bounded by the actual mixed fine-source/coarse-target
common heat exponent.

This module uses those two ordered facts to split the exponent exactly into

`distance heat + component slack + complementary heat reserve`.

The old residual power is then factored into the latter two powers, and the
entire refined global carrier is rewritten with that factorization.  The
reserve is intentionally not called an exterior partition: it also contains
unused Casimir strength and fine faces outside the dyadic packet image.  A
later fiber compiler must identify which part contracts into terminal data.

Constructive contract: natural subtraction guarded by explicit inequalities
and exact rational-power algebra only; no classical choice, proof hole,
trusted external computation, noncomputable declaration, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
open YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem nat_sub_split_local
    {distance component total : Nat}
    (hdistance : distance ≤ component)
    (hcomponent : component ≤ total) :
    total - distance =
      (component - distance) + (total - component) := by
  omega

/-! ## 1. Geometry, component activity, and actual heat -/

def finePacketGlobalNonzeroConnectedEntryDistance
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  linfDist
    (slabPlaquetteAt S.coarse.extent observableFaceId)
    (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1

def finePacketGlobalNonzeroConnectedEntryComponentActivity
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketOrientedObservableJointActivityMass
    S orientation entry.1.sources.1.1 entry.1.sources.2.1
      entry.1.targets observableFaceId

def finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  3 * finePacketGlobalNonzeroConnectedEntryComponentActivity
    S orientation observableFaceId entry

def finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketOrientedJointCommonRateExponent
    S orientation entry.1.sources.1.1 entry.1.sources.2.1 entry.1.targets

/-- The literal target-support component, rather than the whole lattice,
already carries enough joint activity to span the observable separation. -/
theorem finePacketGlobalNonzeroConnectedEntry_distance_le_componentActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace entry ≤
      finePacketGlobalNonzeroConnectedEntryComponentActivity
        S orientation observableFaceId entry := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  have hgeometry :=
    finePacketObservableConnectedDisagreementPath_size_floor
      S entry.1.sources.1.1 entry.1.sources.2.1 observableFaceId
        hobservableFace entry.1.targets path
  have hplaquettes :=
    finePacketObservableTargetSupportPlaquettes_length_le_component
      S entry.1.targets observableFaceId
  have hactivity :=
    finePacketOrientedObservableComponent_length_le_jointActivity
      S hfineCutoff orientation entry.1.sources.1 entry.1.sources.2
        entry.1.targets
        (finePacketGlobalOrientedNonzeroConnectedEntryLowering
          S hfineCutoff orientation observableFaceId entry)
        observableFaceId hobservableFace path.observable_targetStates_ne
  exact Nat.le_trans hgeometry (Nat.le_trans hplaquettes hactivity)

/-- Three heat units per component-activity unit fit inside the actual
fine-source occupation plus coarse SU(2) Casimir-excess exponent. -/
theorem finePacketGlobalNonzeroConnectedEntry_componentHeatCharge_le_common
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
        S orientation observableFaceId entry ≤
      finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
        S orientation observableFaceId entry := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  have hcomponent :=
    finePacketOrientedObservableJointActivityMass_le_total
      S orientation entry.1.sources.1.1 entry.1.sources.2.1
        entry.1.targets observableFaceId hobservableFace
          path.observable_targetStates_ne
  have hsplit :=
    finePacketOrientedTotalJointActivity_eq_source_add_targetExcitation
      S orientation entry.1.sources.1.1 entry.1.sources.2.1 entry.1.targets
  have hsource :=
    finePacketOrientedTotalSourceActivity_le_occupiedFaceCounts
      S hfineCutoff orientation entry.1.sources.1 entry.1.sources.2
  have htarget :=
    eight_mul_finePacketOrientedTotalTargetExcitationActivity_le_excess
      S hfineCutoff orientation entry.1.sources.1 entry.1.sources.2
        entry.1.targets
        (finePacketGlobalOrientedNonzeroConnectedEntryLowering
          S hfineCutoff orientation observableFaceId entry)
  unfold finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
    finePacketGlobalNonzeroConnectedEntryComponentActivity
    finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
    finePacketOrientedJointCommonRateExponent
  omega

/-! ## 2. Exact three-part natural-number budget -/

def finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  3 * finePacketGlobalNonzeroConnectedEntryDistance
    S orientation observableFaceId hobservableFace entry

def finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
      S orientation observableFaceId entry -
    finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
      S orientation observableFaceId hobservableFace entry

def finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
      S orientation observableFaceId entry -
    finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
      S orientation observableFaceId entry

theorem finePacketGlobalNonzeroConnectedEntry_distance_add_componentSlack_eq_componentHeat
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
        S orientation observableFaceId hobservableFace entry +
      finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
        S orientation observableFaceId hobservableFace entry =
      finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
        S orientation observableFaceId entry := by
  apply Nat.add_sub_of_le
  unfold finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
    finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
  exact Nat.mul_le_mul_left 3
    (finePacketGlobalNonzeroConnectedEntry_distance_le_componentActivity
      S hfineCutoff orientation observableFaceId hobservableFace entry)

theorem finePacketGlobalNonzeroConnectedEntry_componentHeat_add_reserve_eq_common
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
        S orientation observableFaceId entry +
      finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
        S orientation observableFaceId entry =
      finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
        S orientation observableFaceId entry := by
  apply Nat.add_sub_of_le
  exact finePacketGlobalNonzeroConnectedEntry_componentHeatCharge_le_common
    S hfineCutoff orientation observableFaceId hobservableFace entry

/-- The old residual exponent is exactly component slack plus the remaining
physical heat reserve. -/
theorem finePacketGlobalNonzeroConnectedEntry_residual_eq_componentSlack_add_reserve
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketOrientedConnectedResidualHeatExponent
        S orientation entry.1.sources.1.1 entry.1.sources.2.1
          observableFaceId entry.1.targets
          (finePacketGlobalConnectedEntryPath
            S observableFaceId hobservableFace entry.1) =
      finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry +
        finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
          S orientation observableFaceId entry := by
  change
    finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
          S orientation observableFaceId entry -
        finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
          S orientation observableFaceId hobservableFace entry =
      (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
            S orientation observableFaceId entry -
          finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
            S orientation observableFaceId hobservableFace entry) +
        (finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
            S orientation observableFaceId entry -
          finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
            S orientation observableFaceId entry)
  apply nat_sub_split_local
  · unfold finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
      finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
    exact Nat.mul_le_mul_left 3
      (finePacketGlobalNonzeroConnectedEntry_distance_le_componentActivity
        S hfineCutoff orientation observableFaceId hobservableFace entry)
  · exact finePacketGlobalNonzeroConnectedEntry_componentHeatCharge_le_common
      S hfineCutoff orientation observableFaceId hobservableFace entry

/-! ## 3. Exact factorization of the refined weight -/

theorem finePacketGlobalNonzeroConnectedEntry_residualPower_eqv_componentSlack_mul_reserve
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    qpow rate
        (finePacketOrientedConnectedResidualHeatExponent
          S orientation entry.1.sources.1.1 entry.1.sources.2.1
            observableFaceId entry.1.targets
            (finePacketGlobalConnectedEntryPath
              S observableFaceId hobservableFace entry.1)) ≈
      qpow rate
          (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
            S orientation observableFaceId hobservableFace entry) *
        qpow rate
          (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
            S orientation observableFaceId entry) := by
  rw [finePacketGlobalNonzeroConnectedEntry_residual_eq_componentSlack_add_reserve
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  exact HeatKernelRGStep.qpow_add rate _ _

def finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Q' :=
  qpow (finePacketJointDistanceFugacity rate)
      (finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace entry) *
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry) *
      (qpow rate
          (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
            S orientation observableFaceId entry) *
        finePacketOrientedGroundNormalizedUnitCongestion
          S hfineCutoff hcoarseCoupling orientation
            entry.1.sources.1 entry.1.sources.2 entry.1.targets))

theorem finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight_eqv_heatBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry ≈
      finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  unfold finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
    finePacketGlobalConnectedEntryRefinedWeight
    finePacketOrientedConnectedDistanceResidualGroundCongestion
    finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
    finePacketGlobalNonzeroConnectedEntryDistance
  dsimp only
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    ((qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
          S orientation observableFaceId entry)) *
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation
          entry.1.sources.1 entry.1.sources.2 entry.1.targets) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketGlobalNonzeroConnectedEntry_residualPower_eqv_componentSlack_mul_reserve
        S hfineCutoff rate orientation observableFaceId hobservableFace entry)
  · exact Q'.mul_assoc_eqv _ _ _

def finePacketGlobalNonzeroConnectedHeatBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace)
    (finePacketGlobalOrientedNonzeroConnectedEntries
      S orientation observableFaceId)

theorem finePacketGlobalOrientedNonzeroConnectedRefinedMass_eqv_heatBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalOrientedNonzeroConnectedEntries
          S orientation observableFaceId) ≈
      finePacketGlobalNonzeroConnectedHeatBudgetMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedHeatBudgetMass
  apply listQSum_congr
  intro entry
  exact
    finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight_eqv_heatBudget
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace entry

theorem finePacketGlobalConnectedEntryNormalizedSum_le_heatBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) ≤
      finePacketGlobalNonzeroConnectedHeatBudgetMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalConnectedEntryNormalizedSum_le_nonzeroRefinedSum
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate orientation
        observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalOrientedNonzeroConnectedRefinedMass_eqv_heatBudget
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace))

/-! ## 4. Axiom audit -/

#print axioms finePacketGlobalNonzeroConnectedEntryDistance
#print axioms finePacketGlobalNonzeroConnectedEntryComponentActivity
#print axioms finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
#print axioms finePacketGlobalNonzeroConnectedEntryCommonHeatExponent
#print axioms finePacketGlobalNonzeroConnectedEntry_distance_le_componentActivity
#print axioms finePacketGlobalNonzeroConnectedEntry_componentHeatCharge_le_common
#print axioms finePacketGlobalNonzeroConnectedEntryDistanceHeatCharge
#print axioms finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
#print axioms finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
#print axioms finePacketGlobalNonzeroConnectedEntry_distance_add_componentSlack_eq_componentHeat
#print axioms finePacketGlobalNonzeroConnectedEntry_componentHeat_add_reserve_eq_common
#print axioms finePacketGlobalNonzeroConnectedEntry_residual_eq_componentSlack_add_reserve
#print axioms finePacketGlobalNonzeroConnectedEntry_residualPower_eqv_componentSlack_mul_reserve
#print axioms finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
#print axioms finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight_eqv_heatBudget
#print axioms finePacketGlobalNonzeroConnectedHeatBudgetMass
#print axioms finePacketGlobalOrientedNonzeroConnectedRefinedMass_eqv_heatBudget
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_heatBudgetMass

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
