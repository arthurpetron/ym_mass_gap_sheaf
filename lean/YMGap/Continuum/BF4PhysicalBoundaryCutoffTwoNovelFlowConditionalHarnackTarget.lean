/-
# The explicit conditional-Harnack target for novel BF4 flow

After cancelling the stationary mass of an edge source, one routed endpoint
pair contributes exactly

  weight(endpointLeft) / weight(edgeSource)
    * weight(endpointRight) * pathLength

when its canonical path traverses the selected directed edge, and zero
otherwise.  This module proves that formula and sums it over the literal novel
endpoint-pair list.  The physical edge-capacity comparison is then equivalent
to bounding this explicit projective-weight/path-incidence sum by the
allocated conditional transition probability.

No projective Harnack estimate, uniform conditional-congestion bound,
thermodynamic/continuum construction, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Relative stationary endpoint weights -/

/-- Stationary weight of an endpoint relative to the positive stationary
weight at an edge source.  It is totalized by zero outside the vacuum-sector
source list. -/
def cutoffTwoNovelEndpointWeightRatioAtSource
    (later source endpoint : Nat) : Q' :=
  if hsource : source ∈ cutoffTwoEdgeLoadFullStates later then
    Q'.divPos
      (cutoffTwoEdgeLoadWeight later endpoint)
      (cutoffTwoEdgeLoadWeight later source)
      (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w :=
          BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
        (hw := by decide) hsource)
  else 0

theorem cutoffTwoNovelEndpointWeightRatioAtSource_nonnegative
    (later source endpoint : Nat) :
    (0 : Q') ≤
      cutoffTwoNovelEndpointWeightRatioAtSource
        later source endpoint := by
  unfold cutoffTwoNovelEndpointWeightRatioAtSource
  by_cases hsource : source ∈ cutoffTwoEdgeLoadFullStates later
  · rw [dif_pos hsource]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (by
        unfold cutoffTwoEdgeLoadWeight centralPhysicalFiniteWeight
        exact centralPhysicalRowMarginal_nonnegative
          (by decide) later 0 _)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (w :=
              BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
            (hw := by decide) hsource)))
  · rw [dif_neg hsource]
    exact Q'.le_refl' 0

theorem cutoffTwoEdgeLoadWeight_mul_endpointRatio_eqv_endpointWeight
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (endpoint : Nat) :
    cutoffTwoEdgeLoadWeight later source *
        cutoffTwoNovelEndpointWeightRatioAtSource
          later source endpoint ≈
      cutoffTwoEdgeLoadWeight later endpoint := by
  have hweight :=
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (hw := by decide) hsource
  unfold cutoffTwoNovelEndpointWeightRatioAtSource
  rw [dif_pos hsource]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (cutoffTwoEdgeLoadWeight later source)
      (Q'.divPos
        (cutoffTwoEdgeLoadWeight later endpoint)
        (cutoffTwoEdgeLoadWeight later source) hweight))
    (Q'.divPos_mul_eqv _ _ hweight)

private theorem divPos_eqv_congr_numerator
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos denominator hdenominator) heq

private theorem divPos_product_eqv_ratio_product
    (left right length denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos ((left * right) * length)
        denominator hdenominator ≈
      (Q'.divPos left denominator hdenominator * right) * length := by
  unfold Q'.divPos
  show ((((left * right) * length) *
      Q'.recipPos denominator hdenominator) : Q') ≈
    (((left * Q'.recipPos denominator hdenominator) * right) * length)
  show
    ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).num *
      ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).den : Int)) =
    ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).num *
      ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).den : Int))
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 2. Exact path-incidence term -/

/-- The explicit conditional-Harnack term for one novel endpoint pair and
one selected directed edge. -/
def cutoffTwoNovelPathPairConditionalHarnackTerm
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈ cutoffTwoNovelEndpointPairs later then
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
        (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    if (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      (cutoffTwoNovelEndpointWeightRatioAtSource
          later source pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0
  else 0

/-- The source-cancelled pair demand is exactly the relative stationary
endpoint product times path length on a traversed edge, and zero otherwise. -/
theorem cutoffTwoNovelPathPairRelativeSourceDemand_eqv_harnackTerm
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairRelativeSourceDemand
        later source target pair ≈
      cutoffTwoNovelPathPairConditionalHarnackTerm
        later source target pair := by
  have hweight :=
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (hw := by decide) hsource
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  unfold cutoffTwoNovelPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  unfold cutoffTwoNovelPathPairConditionalHarnackTerm
  rw [dif_pos hpair]
  change Q'.divPos
      (cutoffTwoNovelPathPairEdgeContribution
        later source target pair)
      (cutoffTwoEdgeLoadWeight later source) hweight ≈
    if (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      (cutoffTwoNovelEndpointWeightRatioAtSource
          later source pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0
  by_cases hedge : (source, target) ∈
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        path
  · rw [if_pos hedge]
    have hcontribution :=
      cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
        later source target pair hpair
    change cutoffTwoNovelPathPairEdgeContribution
        later source target pair ≈
      if (source, target) ∈
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path then
        (cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat
            (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              path)
      else 0 at hcontribution
    rw [if_pos hedge] at hcontribution
    refine Q'.eqv_trans _
      (Q'.divPos
        ((cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat
            (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              path))
        (cutoffTwoEdgeLoadWeight later source) hweight) _ ?_ ?_
    · exact divPos_eqv_congr_numerator hweight hcontribution
    have hratio :
        Q'.divPos
            (cutoffTwoEdgeLoadWeight later pair.1)
            (cutoffTwoEdgeLoadWeight later source) hweight =
          cutoffTwoNovelEndpointWeightRatioAtSource
            later source pair.1 := by
      unfold cutoffTwoNovelEndpointWeightRatioAtSource
      rw [dif_pos hsource]
    rw [← hratio]
    exact divPos_product_eqv_ratio_product _ _ _ _ hweight
  · rw [if_neg hedge]
    have hcontribution :=
      cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
        later source target pair hpair
    change cutoffTwoNovelPathPairEdgeContribution
        later source target pair ≈
      if (source, target) ∈
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path then
        (cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat
            (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              path)
      else 0 at hcontribution
    rw [if_neg hedge] at hcontribution
    refine Q'.eqv_trans _
      (Q'.divPos 0
        (cutoffTwoEdgeLoadWeight later source) hweight) _
      (divPos_eqv_congr_numerator hweight hcontribution) ?_
    unfold Q'.divPos
    exact Q'.zero_mul_eqv _

/-! ## 3. The exact summed Harnack target -/

def cutoffTwoNovelConditionalHarnackLoad
    (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalHarnackTerm
      later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoNovelRelativeSourceEdgeLoad later source target ≈
      cutoffTwoNovelConditionalHarnackLoad
        later source target := by
  unfold cutoffTwoNovelRelativeSourceEdgeLoad
    cutoffTwoNovelConditionalHarnackLoad
  apply listQSum_congr_on
  intro pair hpair
  exact cutoffTwoNovelPathPairRelativeSourceDemand_eqv_harnackTerm
    hsource target pair hpair

/-- The original physical edge capacity is equivalent to the explicit
conditional-Harnack path-incidence inequality. -/
theorem cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target) ↔
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalHarnackLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) := by
  constructor
  · intro hcapacity
    have hrelative :=
      (cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion
        hsource target).mp hcapacity
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (Q'.eqv_symm
            (cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
              hsource target))))
      hrelative
  · intro hharnack
    apply
      (cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion
        hsource target).mpr
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
            hsource target)))
      hharnack

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_conditionalHarnack
    (later : Nat)
    (hharnack : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalHarnackLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_relativeConditional
  intro source hsource target htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
          hsource target)))
    (hharnack source hsource target htarget)

structure CutoffTwoCofinalNovelConditionalHarnackBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  harnack : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelConditionalHarnackLoad
          (anchor request) source target ≤
      cutoffTwoNovelAllocatedConditionalKernel
        (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalHarnackBound

def toCofinalNovelFlowCapacityRatio
    (bound : CutoffTwoCofinalNovelConditionalHarnackBound) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_conditionalHarnack
      (bound.anchor request)
      (bound.harnack request)

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalHarnackBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalHarnackBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.cutoffTwoEdgeLoadWeight_mul_endpointRatio_eqv_endpointWeight
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.cutoffTwoNovelPathPairRelativeSourceDemand_eqv_harnackTerm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.CutoffTwoCofinalNovelConditionalHarnackBound.toCompletedStrictContractionData
