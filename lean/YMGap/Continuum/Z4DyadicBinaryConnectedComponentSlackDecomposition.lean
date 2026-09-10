/-
# Split connected-component slack into geometry and local activity

The component heat slack of the preceding module is three times

`component activity - observable separation`.

The literal target-support component has a size between those two numbers:
the geometric path proves `distance <= component size`, while positivity and
lowering prove `component size <= component activity`.  Hence the slack
splits exactly into

* geometric detour: three times `component size - distance`; and
* local activity excess: three times `component activity - component size`.

This is the separation needed by the entropy argument.  Lattice-animal
shape multiplicity should be paid by detour heat, while the finite SU(2)
local-state code should be paid by activity-excess heat.

Constructive contract: guarded natural subtraction and exact rational-power
algebra only; no classical choice, proof hole, trusted external computation,
noncomputable declaration, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor

local infix:50 " ≈ " => Q'.eqv

private theorem scaled_sub_split_local
    {distance size activity : Nat}
    (hdistance : distance ≤ size) (hsize : size ≤ activity) :
    3 * activity - 3 * distance =
      3 * (size - distance) + 3 * (activity - size) := by
  omega

/-! ## 1. Component size lies between distance and activity -/

def finePacketGlobalNonzeroConnectedEntryComponentSize
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  (finePacketGlobalConnectedEntryTargetComponent
    S observableFaceId entry.1).length

theorem finePacketGlobalNonzeroConnectedEntry_distance_le_componentSize
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace entry ≤
      finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId entry := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  exact Nat.le_trans
    (finePacketObservableConnectedDisagreementPath_size_floor
      S entry.1.sources.1.1 entry.1.sources.2.1 observableFaceId
        hobservableFace entry.1.targets path)
    (finePacketObservableTargetSupportPlaquettes_length_le_component
      S entry.1.targets observableFaceId)

theorem finePacketGlobalNonzeroConnectedEntry_componentSize_le_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId entry ≤
      finePacketGlobalNonzeroConnectedEntryComponentActivity
        S orientation observableFaceId entry := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  exact finePacketOrientedObservableComponent_length_le_jointActivity
    S hfineCutoff orientation entry.1.sources.1 entry.1.sources.2
      entry.1.targets
      (finePacketGlobalOrientedNonzeroConnectedEntryLowering
        S hfineCutoff orientation observableFaceId entry)
      observableFaceId hobservableFace path.observable_targetStates_ne

/-! ## 2. Exact geometric and local-activity slack -/

def finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  3 * (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry -
        finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry)

def finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Nat :=
  3 * (finePacketGlobalNonzeroConnectedEntryComponentActivity
          S orientation observableFaceId entry -
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry)

/-- Component heat slack is exactly shape detour plus local-state excess. -/
theorem finePacketGlobalNonzeroConnectedEntry_componentSlack_eq_detour_add_activityExcess
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
        S orientation observableFaceId hobservableFace entry =
      finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
          S orientation observableFaceId hobservableFace entry +
        finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
          S orientation observableFaceId entry := by
  change
    3 * finePacketGlobalNonzeroConnectedEntryComponentActivity
          S orientation observableFaceId entry -
        3 * finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry =
      3 * (finePacketGlobalNonzeroConnectedEntryComponentSize
              S orientation observableFaceId entry -
            finePacketGlobalNonzeroConnectedEntryDistance
              S orientation observableFaceId hobservableFace entry) +
        3 * (finePacketGlobalNonzeroConnectedEntryComponentActivity
              S orientation observableFaceId entry -
            finePacketGlobalNonzeroConnectedEntryComponentSize
              S orientation observableFaceId entry)
  exact scaled_sub_split_local
    (finePacketGlobalNonzeroConnectedEntry_distance_le_componentSize
      S orientation observableFaceId hobservableFace entry)
    (finePacketGlobalNonzeroConnectedEntry_componentSize_le_activity
      S hfineCutoff orientation observableFaceId hobservableFace entry)

theorem finePacketGlobalNonzeroConnectedEntry_componentSlackPower_eqv_detour_mul_activityExcess
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry) ≈
      qpow rate
          (finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
            S orientation observableFaceId hobservableFace entry) *
        qpow rate
          (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
            S orientation observableFaceId entry) := by
  rw [finePacketGlobalNonzeroConnectedEntry_componentSlack_eq_detour_add_activityExcess
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  exact HeatKernelRGStep.qpow_add rate _ _

/-! ## 3. Rewrite the complete carrier with the two distinct entropy funds -/

def finePacketGlobalNonzeroConnectedEntryStructuredHeatWeight
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
        (finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
          S orientation observableFaceId hobservableFace entry) *
      (qpow rate
          (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
            S orientation observableFaceId entry) *
        (qpow rate
            (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
              S orientation observableFaceId entry) *
          finePacketOrientedGroundNormalizedUnitCongestion
            S hfineCutoff hcoarseCoupling orientation
              entry.1.sources.1 entry.1.sources.2 entry.1.targets)))

theorem finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_structured
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry ≈
      finePacketGlobalNonzeroConnectedEntryStructuredHeatWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  unfold finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
    finePacketGlobalNonzeroConnectedEntryStructuredHeatWeight
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    ((qpow rate
        (finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
          S orientation observableFaceId hobservableFace entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
          S orientation observableFaceId entry)) *
      (qpow rate
          (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
            S orientation observableFaceId entry) *
        finePacketOrientedGroundNormalizedUnitCongestion
          S hfineCutoff hcoarseCoupling orientation
            entry.1.sources.1 entry.1.sources.2 entry.1.targets)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketGlobalNonzeroConnectedEntry_componentSlackPower_eqv_detour_mul_activityExcess
        S hfineCutoff rate orientation observableFaceId hobservableFace entry)
  · exact Q'.mul_assoc_eqv _ _ _

def finePacketGlobalNonzeroConnectedStructuredHeatMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedEntryStructuredHeatWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace)
    (finePacketGlobalOrientedNonzeroConnectedEntries
      S orientation observableFaceId)

theorem finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_structured
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNonzeroConnectedHeatBudgetMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≈
      finePacketGlobalNonzeroConnectedStructuredHeatMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedHeatBudgetMass
    finePacketGlobalNonzeroConnectedStructuredHeatMass
  apply listQSum_congr
  intro entry
  exact finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_structured
    S hfineCutoff hcoarseCoupling rate orientation observableFaceId
      hobservableFace entry

theorem finePacketGlobalConnectedEntryNormalizedSum_le_structuredHeatMass
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
      finePacketGlobalNonzeroConnectedStructuredHeatMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalConnectedEntryNormalizedSum_le_heatBudgetMass
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate orientation
        observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_structured
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace))

/-! ## 4. Axiom audit -/

#print axioms finePacketGlobalNonzeroConnectedEntryComponentSize
#print axioms finePacketGlobalNonzeroConnectedEntry_distance_le_componentSize
#print axioms finePacketGlobalNonzeroConnectedEntry_componentSize_le_activity
#print axioms finePacketGlobalNonzeroConnectedEntryGeometricDetourHeat
#print axioms finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
#print axioms finePacketGlobalNonzeroConnectedEntry_componentSlack_eq_detour_add_activityExcess
#print axioms finePacketGlobalNonzeroConnectedEntry_componentSlackPower_eqv_detour_mul_activityExcess
#print axioms finePacketGlobalNonzeroConnectedEntryStructuredHeatWeight
#print axioms finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_structured
#print axioms finePacketGlobalNonzeroConnectedStructuredHeatMass
#print axioms finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_structured
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_structuredHeatMass

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
