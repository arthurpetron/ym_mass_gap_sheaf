/-
# Stationary-weight envelope for the cutoff-two conditional ratio ceiling

Detailed balance identifies every positive-edge reverse/forward conditional
ratio with the stationary-weight ratio across the same edge.  This module
lifts that pointwise identity through the located finite maximum, then bounds
the positive-edge maximum by the simpler maximum over all ordered stationary
weight ratios on the finite carrier.

The ratio-ceiling load is proved monotone in its ceiling.  Consequently,
payment of the all-pairs stationary envelope is a sufficient, explicitly
stationary formulation of the novel-flow capacity frontier and still compiles
to completed strict contraction along a cofinal schedule.

The all-pairs stationary envelope may grow with the cutoff, and no payment
bound is proved here.  No uniform gap, thermodynamic/continuum construction,
or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Detailed balance identifies the positive-edge maximum -/

/-- Stationary-weight ratio on a positive physical edge, totalized by zero
away from the finite carrier or away from positive edges. -/
def cutoffTwoPositiveEdgeStationaryWeightRatio
    (later left right : Nat) : Q' :=
  if hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      if _hforward : (0 : Q') <
          cutoffTwoEdgeLoadKernel later left right then
        Q'.divPos
          (cutoffTwoEdgeLoadWeight later left)
          (cutoffTwoEdgeLoadWeight later right)
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w :=
              BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
            (hw := by decide) hright)
      else 0
    else 0
  else 0

theorem cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio
    (later left right : Nat) :
    cutoffTwoConditionalReverseForwardRatio later left right ≈
      cutoffTwoPositiveEdgeStationaryWeightRatio later left right := by
  unfold cutoffTwoConditionalReverseForwardRatio
    cutoffTwoPositiveEdgeStationaryWeightRatio
  by_cases hleft : left ∈ cutoffTwoEdgeLoadFullStates later
  · rw [dif_pos hleft, dif_pos hleft]
    by_cases hright : right ∈ cutoffTwoEdgeLoadFullStates later
    · rw [dif_pos hright, dif_pos hright]
      by_cases hforward : (0 : Q') <
          cutoffTwoEdgeLoadKernel later left right
      · rw [dif_pos hforward, dif_pos hforward]
        exact Q'.eqv_symm
          (cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
            hleft hright hforward)
      · rw [dif_neg hforward, dif_neg hforward]
        exact Q'.eqv_refl 0
    · rw [dif_neg hright, dif_neg hright]
      exact Q'.eqv_refl 0
  · rw [dif_neg hleft, dif_neg hleft]
    exact Q'.eqv_refl 0

/-- Located maximum of stationary-weight ratios restricted to positive
physical edges. -/
def cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling
    (later : Nat) : Q' :=
  listQMaxZero
    (fun pair : Nat × Nat =>
      cutoffTwoPositiveEdgeStationaryWeightRatio
        later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))

/-- The previously constructed conditional-ratio ceiling is exactly, in the
rational setoid, the finite positive-edge stationary-weight-ratio maximum. -/
theorem cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_positiveEdgeStationaryWeightFiniteCeiling
    (later : Nat) :
    cutoffTwoConditionalReverseForwardFiniteCeiling later ≈
      cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardFiniteCeiling
    cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling
  apply Q'.eqv_of_le_le
  · apply listQMaxZero_mono
    intro pair
    exact Q'.le_of_eqv
      (cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio
        later pair.1 pair.2)
  · apply listQMaxZero_mono
    intro pair
    exact Q'.ge_of_eqv
      (cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio
        later pair.1 pair.2)

/-! ## 2. The all-pairs stationary-ratio envelope -/

/-- Stationary-weight ratio on an ordered carrier pair, totalized by zero
away from the finite carrier. -/
def cutoffTwoStationaryWeightRatio
    (later left right : Nat) : Q' :=
  if _hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      Q'.divPos
        (cutoffTwoEdgeLoadWeight later left)
        (cutoffTwoEdgeLoadWeight later right)
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (w :=
            BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
          (hw := by decide) hright)
    else 0
  else 0

theorem cutoffTwoStationaryWeightRatio_nonnegative
    (later left right : Nat) :
    (0 : Q') ≤ cutoffTwoStationaryWeightRatio later left right := by
  unfold cutoffTwoStationaryWeightRatio
  split
  · split
    · unfold Q'.divPos
      exact Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w :=
              BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
            (hw := by decide) ‹left ∈ cutoffTwoEdgeLoadFullStates later›))
        (Q'.le_of_lt (Q'.recipPos_pos _ _))
    · exact Q'.le_refl' 0
  · exact Q'.le_refl' 0

theorem cutoffTwoPositiveEdgeStationaryWeightRatio_le_stationaryWeightRatio
    (later left right : Nat) :
    cutoffTwoPositiveEdgeStationaryWeightRatio later left right ≤
      cutoffTwoStationaryWeightRatio later left right := by
  unfold cutoffTwoPositiveEdgeStationaryWeightRatio
    cutoffTwoStationaryWeightRatio
  by_cases hleft : left ∈ cutoffTwoEdgeLoadFullStates later
  · rw [dif_pos hleft, dif_pos hleft]
    by_cases hright : right ∈ cutoffTwoEdgeLoadFullStates later
    · rw [dif_pos hright, dif_pos hright]
      by_cases hforward : (0 : Q') <
          cutoffTwoEdgeLoadKernel later left right
      · rw [dif_pos hforward]
        exact Q'.le_refl' _
      · rw [dif_neg hforward]
        unfold Q'.divPos
        exact Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
              (w :=
                BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
              (hw := by decide) hleft))
          (Q'.le_of_lt (Q'.recipPos_pos _ _))
    · rw [dif_neg hright, dif_neg hright]
      exact Q'.le_refl' 0
  · rw [dif_neg hleft, dif_neg hleft]
    exact Q'.le_refl' 0

/-- Located maximum over all ordered stationary-weight ratios.  Unlike the
positive-edge maximum, this expression no longer depends on the support of
the transition kernel. -/
def cutoffTwoStationaryWeightRatioFiniteEnvelope
    (later : Nat) : Q' :=
  listQMaxZero
    (fun pair : Nat × Nat =>
      cutoffTwoStationaryWeightRatio later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))

theorem cutoffTwoStationaryWeightRatioFiniteEnvelope_nonnegative
    (later : Nat) :
    (0 : Q') ≤ cutoffTwoStationaryWeightRatioFiniteEnvelope later := by
  unfold cutoffTwoStationaryWeightRatioFiniteEnvelope
  apply listQMaxZero_nonnegative
  intro pair
  exact cutoffTwoStationaryWeightRatio_nonnegative
    later pair.1 pair.2

/-- The exact conditional-ratio ceiling lies below the simpler all-pairs
stationary-weight envelope. -/
theorem cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope
    (later : Nat) :
    cutoffTwoConditionalReverseForwardFiniteCeiling later ≤
      cutoffTwoStationaryWeightRatioFiniteEnvelope later := by
  have hedgeMaximum :
      cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling later ≤
        cutoffTwoStationaryWeightRatioFiniteEnvelope later := by
    unfold cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling
      cutoffTwoStationaryWeightRatioFiniteEnvelope
    apply listQMaxZero_mono
    intro pair
    exact
      cutoffTwoPositiveEdgeStationaryWeightRatio_le_stationaryWeightRatio
        later pair.1 pair.2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_positiveEdgeStationaryWeightFiniteCeiling
        later))
    hedgeMaximum

def cutoffTwoStationaryWeightRatioFiniteEnvelopeData
    (later : Nat) :
    CutoffTwoConditionalReverseForwardCeilingAt later
      (cutoffTwoStationaryWeightRatioFiniteEnvelope later) where
  rho_nonnegative :=
    cutoffTwoStationaryWeightRatioFiniteEnvelope_nonnegative later
  ratio_le := fun _left hleft _right hright hforward =>
    Q'.le_trans' _ _ _
      (cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
        hleft hright hforward)
      (cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope
        later)

/-! ## 3. Monotonicity of the ceiling-weighted path load -/

private theorem qpow_base_mono_local
    {rho sigma : Q'} (hrho : (0 : Q') ≤ rho)
    (hle : rho ≤ sigma) :
    ∀ exponent : Nat, rho ^ exponent ≤ sigma ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hsigma : (0 : Q') ≤ sigma :=
        Q'.le_trans' _ _ _ hrho hle
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hle
          (Q'.pow_nonneg rho hrho exponent))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (qpow_base_mono_local hrho hle exponent) hsigma)

theorem cutoffTwoNovelPathPairConditionalRatioCeilingTerm_mono
    {rho sigma : Q'}
    (hrho : (0 : Q') ≤ rho) (hle : rho ≤ sigma)
    (later source target : Nat) (pair : Nat × Nat) :
    cutoffTwoNovelPathPairConditionalRatioCeilingTerm
        rho later source target pair ≤
      cutoffTwoNovelPathPairConditionalRatioCeilingTerm
        sigma later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalRatioCeilingTerm
  by_cases hpair : pair ∈ cutoffTwoNovelEndpointPairs later
  · rw [dif_pos hpair, dif_pos hpair]
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
        (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    change
      (if hedge : (source, target) ∈
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path then
        let pathPrefixData :=
          BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.PositiveKernelChainIn.prefixAtDirectedEdge
            (cutoffTwoNovelEndpointPair_mem_full hpair).1
            path (source, target) hedge
        (rho ^
            BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              pathPrefixData.pathPrefix *
          cutoffTwoEdgeLoadWeight later pair.2) *
        Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path)
      else 0) ≤
      (if hedge : (source, target) ∈
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path then
        let pathPrefixData :=
          BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.PositiveKernelChainIn.prefixAtDirectedEdge
            (cutoffTwoNovelEndpointPair_mem_full hpair).1
            path (source, target) hedge
        (sigma ^
            BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              pathPrefixData.pathPrefix *
          cutoffTwoEdgeLoadWeight later pair.2) *
        Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path)
      else 0)
    by_cases hedge : (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path
    · rw [dif_pos hedge, dif_pos hedge]
      let pathPrefixData :=
        BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
      have hpower := qpow_base_mono_local hrho hle
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          pathPrefixData.pathPrefix)
      have hweight : (0 : Q') ≤ cutoffTwoEdgeLoadWeight later pair.2 :=
        Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w :=
              BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
            (hw := by decide)
            (cutoffTwoNovelEndpointPair_mem_full hpair).2)
      have hlength : (0 : Q') ≤ Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path) :=
        ExpNeg.ofNat_nonneg' _
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hpower hweight)
        hlength
    · rw [dif_neg hedge, dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair, dif_neg hpair]
    exact Q'.le_refl' 0

theorem cutoffTwoNovelConditionalRatioCeilingLoad_mono
    {rho sigma : Q'}
    (hrho : (0 : Q') ≤ rho) (hle : rho ≤ sigma)
    (later source target : Nat) :
    cutoffTwoNovelConditionalRatioCeilingLoad
        rho later source target ≤
      cutoffTwoNovelConditionalRatioCeilingLoad
        sigma later source target := by
  unfold cutoffTwoNovelConditionalRatioCeilingLoad
  apply listQSum_mono
  intro pair _hpair
  exact cutoffTwoNovelPathPairConditionalRatioCeilingTerm_mono
    hrho hle later source target pair

def cutoffTwoNovelConditionalStationaryRatioEnvelopeLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelConditionalRatioCeilingLoad
    (cutoffTwoStationaryWeightRatioFiniteEnvelope later)
    later source target

theorem cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_stationaryRatioEnvelopeLoad
    (later source target : Nat) :
    cutoffTwoNovelConditionalFiniteRatioCeilingLoad
        later source target ≤
      cutoffTwoNovelConditionalStationaryRatioEnvelopeLoad
        later source target := by
  unfold cutoffTwoNovelConditionalFiniteRatioCeilingLoad
    cutoffTwoNovelConditionalStationaryRatioEnvelopeLoad
  exact cutoffTwoNovelConditionalRatioCeilingLoad_mono
    (cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative later)
    (cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope
      later)
    later source target

/-! ## 4. Stationary-envelope payment compiler -/

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_stationaryRatioEnvelope
    (later : Nat)
    (henvelope : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalStationaryRatioEnvelopeLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    (cutoffTwoStationaryWeightRatioFiniteEnvelopeData later)
  exact henvelope

structure CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound : Type 1 where
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
          cutoffTwoNovelConditionalStationaryRatioEnvelopeLoad
            (anchor request) source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound

def toCofinalNovelConditionalRatioCeilingBound
    (bound :
      CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun request =>
    cutoffTwoStationaryWeightRatioFiniteEnvelope
      (bound.anchor request)
  local_ceiling := fun request =>
    cutoffTwoStationaryWeightRatioFiniteEnvelopeData
      (bound.anchor request)
  ceiling_capacity := fun request => bound.envelope_capacity request

def toCompletedStrictContractionData
    (bound :
      CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_positiveEdgeStationaryWeightFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoNovelConditionalRatioCeilingLoad_mono
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_stationaryRatioEnvelopeLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_stationaryRatioEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound.toCompletedStrictContractionData
