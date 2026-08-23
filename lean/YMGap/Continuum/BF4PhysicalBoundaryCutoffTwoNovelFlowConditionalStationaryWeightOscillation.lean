/-
# Stationary-weight oscillation bound for the cutoff-two novel-flow ceiling

The all-pairs stationary-ratio envelope is controlled by two literal finite
statistics: the maximum stationary weight and the positive minimum stationary
weight on the vacuum-sector carrier.  This module constructs both statistics
and proves

  stationaryRatioEnvelope <= maximumWeight / minimumWeight
                           <= 1 / minimumWeight.

The second inequality uses normalization: the vacuum-sector mass is at most
one, so every carrier weight and hence its maximum is at most one.  Monotonicity
of the previously constructed ceiling load transports these scalar bounds to
the novel-flow payment compiler.

This isolates a deliberately coarse sufficient route.  No cutoff-uniform
positive minimum is proved, and a shrinking minimum can make the reciprocal
envelope useless even when the sharper adjacent-edge oscillation remains
controlled.  No uniform gap, thermodynamic/continuum construction, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
import YMGap.Continuum.FusionMarginMono

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Located maximum and positive minimum of stationary weights -/

def cutoffTwoStationaryWeightFiniteMaximum (later : Nat) : Q' :=
  listQMaxZero
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadFullStates later)

def cutoffTwoStationaryWeightFiniteMinimum (later : Nat) : Q' :=
  listPositiveMinOne
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadFullStates later)

theorem cutoffTwoStationaryWeightFiniteMaximum_nonnegative
    (later : Nat) :
    (0 : Q') ≤ cutoffTwoStationaryWeightFiniteMaximum later := by
  unfold cutoffTwoStationaryWeightFiniteMaximum
  apply listQMaxZero_nonnegative
  intro state
  unfold cutoffTwoEdgeLoadWeight
  exact BF4SU2FixedMagneticPhysicalMarkov.centralPhysicalRowMarginal_nonnegative
    (by decide) later 0 _

theorem cutoffTwoStationaryWeightFiniteMinimum_pos
    (later : Nat) :
    (0 : Q') < cutoffTwoStationaryWeightFiniteMinimum later := by
  unfold cutoffTwoStationaryWeightFiniteMinimum
  apply listPositiveMinOne_pos
  intro state hstate
  exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hstate

theorem cutoffTwoStationaryWeight_le_finiteMaximum
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoEdgeLoadWeight later state ≤
      cutoffTwoStationaryWeightFiniteMaximum later := by
  unfold cutoffTwoStationaryWeightFiniteMaximum
  exact le_listQMaxZero_of_mem
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadFullStates later) hstate

theorem cutoffTwoStationaryWeightFiniteMinimum_le
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoStationaryWeightFiniteMinimum later ≤
      cutoffTwoEdgeLoadWeight later state := by
  unfold cutoffTwoStationaryWeightFiniteMinimum
  exact listPositiveMinOne_le_of_mem
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadFullStates later) state hstate

/-- The finite maximum is bounded by the total vacuum-sector stationary mass. -/
theorem cutoffTwoStationaryWeightFiniteMaximum_le_sectorMass
    (later : Nat) :
    cutoffTwoStationaryWeightFiniteMaximum later ≤
      centralPhysicalFiniteVacuumSectorMass
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
        (by decide) later 0 := by
  unfold cutoffTwoStationaryWeightFiniteMaximum
    centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
    cutoffTwoEdgeLoadFullStates cutoffTwoEdgeLoadWeight
  apply listQMaxZero_le_listQSum_of_nonnegative
  intro state
  exact BF4SU2FixedMagneticPhysicalMarkov.centralPhysicalRowMarginal_nonnegative
    (by decide) later 0 _

/-- Normalization of the full physical stationary law bounds every finite
vacuum-sector maximum by one. -/
theorem cutoffTwoStationaryWeightFiniteMaximum_le_one
    (later : Nat) :
    cutoffTwoStationaryWeightFiniteMaximum later ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (cutoffTwoStationaryWeightFiniteMaximum_le_sectorMass later)
    (cutoffTwoFullSectorMass_le_one later)

/-! ## 2. Oscillation quotient bounds the all-pairs ratio envelope -/

def cutoffTwoStationaryWeightMaxMinEnvelope (later : Nat) : Q' :=
  Q'.divPos
    (cutoffTwoStationaryWeightFiniteMaximum later)
    (cutoffTwoStationaryWeightFiniteMinimum later)
    (cutoffTwoStationaryWeightFiniteMinimum_pos later)

theorem cutoffTwoStationaryWeightMaxMinEnvelope_nonnegative
    (later : Nat) :
    (0 : Q') ≤ cutoffTwoStationaryWeightMaxMinEnvelope later := by
  unfold cutoffTwoStationaryWeightMaxMinEnvelope Q'.divPos
  exact Q'.mul_nonneg _ _
    (cutoffTwoStationaryWeightFiniteMaximum_nonnegative later)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem cutoffTwoStationaryWeightRatio_le_maxMinEnvelope
    (later left right : Nat) :
    cutoffTwoStationaryWeightRatio later left right ≤
      cutoffTwoStationaryWeightMaxMinEnvelope later := by
  unfold cutoffTwoStationaryWeightRatio
  by_cases hleft : left ∈ cutoffTwoEdgeLoadFullStates later
  · rw [dif_pos hleft]
    by_cases hright : right ∈ cutoffTwoEdgeLoadFullStates later
    · rw [dif_pos hright]
      apply FusionMarginMono.divPos_le_divPos_of_cross
      have hminimum0 : (0 : Q') ≤
          cutoffTwoStationaryWeightFiniteMinimum later :=
        Q'.le_of_lt (cutoffTwoStationaryWeightFiniteMinimum_pos later)
      have hmaximum0 : (0 : Q') ≤
          cutoffTwoStationaryWeightFiniteMaximum later :=
        cutoffTwoStationaryWeightFiniteMaximum_nonnegative later
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (cutoffTwoStationaryWeight_le_finiteMaximum hleft)
          hminimum0)
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (cutoffTwoStationaryWeightFiniteMinimum_le hright)
          hmaximum0)
    · rw [dif_neg hright]
      exact cutoffTwoStationaryWeightMaxMinEnvelope_nonnegative later
  · rw [dif_neg hleft]
    exact cutoffTwoStationaryWeightMaxMinEnvelope_nonnegative later

private theorem listQMaxZero_le_of_forall_local
    {State : Type} (value : State → Q') (bound : Q')
    (hbound : (0 : Q') ≤ bound) :
    ∀ states : List State,
      (∀ state, state ∈ states → value state ≤ bound) →
      listQMaxZero value states ≤ bound
  | [], _ => hbound
  | first :: rest, hall => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ bound).mpr
      exact ⟨hall first List.mem_cons_self,
        listQMaxZero_le_of_forall_local value bound hbound rest
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))⟩

theorem cutoffTwoStationaryWeightRatioFiniteEnvelope_le_maxMinEnvelope
    (later : Nat) :
    cutoffTwoStationaryWeightRatioFiniteEnvelope later ≤
      cutoffTwoStationaryWeightMaxMinEnvelope later := by
  unfold cutoffTwoStationaryWeightRatioFiniteEnvelope
  apply listQMaxZero_le_of_forall_local
    (fun pair : Nat × Nat =>
      cutoffTwoStationaryWeightRatio later pair.1 pair.2)
    (cutoffTwoStationaryWeightMaxMinEnvelope later)
    (cutoffTwoStationaryWeightMaxMinEnvelope_nonnegative later)
  intro pair _hpair
  exact cutoffTwoStationaryWeightRatio_le_maxMinEnvelope
    later pair.1 pair.2

/-! ## 3. The coarse reciprocal-minimum envelope -/

def cutoffTwoStationaryWeightReciprocalMinimumEnvelope
    (later : Nat) : Q' :=
  Q'.divPos 1
    (cutoffTwoStationaryWeightFiniteMinimum later)
    (cutoffTwoStationaryWeightFiniteMinimum_pos later)

theorem cutoffTwoStationaryWeightReciprocalMinimumEnvelope_nonnegative
    (later : Nat) :
    (0 : Q') ≤
      cutoffTwoStationaryWeightReciprocalMinimumEnvelope later := by
  unfold cutoffTwoStationaryWeightReciprocalMinimumEnvelope Q'.divPos
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem cutoffTwoStationaryWeightMaxMinEnvelope_le_reciprocalMinimumEnvelope
    (later : Nat) :
    cutoffTwoStationaryWeightMaxMinEnvelope later ≤
      cutoffTwoStationaryWeightReciprocalMinimumEnvelope later := by
  unfold cutoffTwoStationaryWeightMaxMinEnvelope
    cutoffTwoStationaryWeightReciprocalMinimumEnvelope
  apply FusionMarginMono.divPos_le_divPos_of_cross
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (cutoffTwoStationaryWeightFiniteMaximum_le_one later)
    (Q'.le_of_lt (cutoffTwoStationaryWeightFiniteMinimum_pos later))

theorem cutoffTwoConditionalReverseForwardFiniteCeiling_le_reciprocalMinimumEnvelope
    (later : Nat) :
    cutoffTwoConditionalReverseForwardFiniteCeiling later ≤
      cutoffTwoStationaryWeightReciprocalMinimumEnvelope later :=
  Q'.le_trans' _ _ _
    (cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope
      later)
    (Q'.le_trans' _ _ _
      (cutoffTwoStationaryWeightRatioFiniteEnvelope_le_maxMinEnvelope later)
      (cutoffTwoStationaryWeightMaxMinEnvelope_le_reciprocalMinimumEnvelope
        later))

def cutoffTwoStationaryWeightReciprocalMinimumEnvelopeData
    (later : Nat) :
    CutoffTwoConditionalReverseForwardCeilingAt later
      (cutoffTwoStationaryWeightReciprocalMinimumEnvelope later) where
  rho_nonnegative :=
    cutoffTwoStationaryWeightReciprocalMinimumEnvelope_nonnegative later
  ratio_le := fun _left hleft _right hright hforward =>
    Q'.le_trans' _ _ _
      (cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
        hleft hright hforward)
      (cutoffTwoConditionalReverseForwardFiniteCeiling_le_reciprocalMinimumEnvelope
        later)

def cutoffTwoNovelConditionalReciprocalMinimumEnvelopeLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelConditionalRatioCeilingLoad
    (cutoffTwoStationaryWeightReciprocalMinimumEnvelope later)
    later source target

theorem cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_reciprocalMinimumEnvelopeLoad
    (later source target : Nat) :
    cutoffTwoNovelConditionalFiniteRatioCeilingLoad
        later source target ≤
      cutoffTwoNovelConditionalReciprocalMinimumEnvelopeLoad
        later source target := by
  unfold cutoffTwoNovelConditionalFiniteRatioCeilingLoad
    cutoffTwoNovelConditionalReciprocalMinimumEnvelopeLoad
  exact cutoffTwoNovelConditionalRatioCeilingLoad_mono
    (cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative later)
    (cutoffTwoConditionalReverseForwardFiniteCeiling_le_reciprocalMinimumEnvelope
      later)
    later source target

/-! ## 4. Reciprocal-minimum payment compiler -/

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_reciprocalMinimumEnvelope
    (later : Nat)
    (henvelope : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalReciprocalMinimumEnvelopeLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    (cutoffTwoStationaryWeightReciprocalMinimumEnvelopeData later)
  exact henvelope

structure CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  envelope_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalReciprocalMinimumEnvelopeLoad
            (anchor request) source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound

def toCofinalNovelConditionalRatioCeilingBound
    (bound :
      CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun request =>
    cutoffTwoStationaryWeightReciprocalMinimumEnvelope
      (bound.anchor request)
  local_ceiling := fun request =>
    cutoffTwoStationaryWeightReciprocalMinimumEnvelopeData
      (bound.anchor request)
  ceiling_capacity := fun request => bound.envelope_capacity request

def toCompletedStrictContractionData
    (bound :
      CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoStationaryWeightFiniteMinimum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoStationaryWeightFiniteMaximum_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoStationaryWeightRatio_le_maxMinEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoStationaryWeightRatioFiniteEnvelope_le_maxMinEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoConditionalReverseForwardFiniteCeiling_le_reciprocalMinimumEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_reciprocalMinimumEnvelopeLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_reciprocalMinimumEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound.toCompletedStrictContractionData
