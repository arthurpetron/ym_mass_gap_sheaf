/-
# Boundary-moment reduction of the cutoff-two novel-flow ceiling

The unnormalised BF4 row mass is a row sum of the physical reflected Gram
kernel.  Reordering its two finite sums expresses it exactly as

  sum_boundary boundaryWeight * sourceAmplitude * totalTargetAmplitude.

The last two factors are the literal half-slab boundary messages.  A
pointwise projective comparison of the source amplitudes across every
positive physical edge therefore bounds the raw row-mass ratio, hence by the
previous normalization cancellation and detailed balance also bounds the
reverse/forward conditional ratio used by the novel-flow path load.

This module constructs that implication and the resulting cofinal payment
compiler.  It does not inhabit the amplitude Harnack comparison, pay the load,
construct a thermodynamic or continuum limit, or prove the Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio
import YMGap.Continuum.BF4PhysicalBoundaryCenteredGram

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact raw row as a boundary-channel moment -/

def cutoffTwoRawBoundaryMomentTerm
    (later state : Nat) (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary *
    (centralHalfAmplitude cutoffTwoHalfCoupling later 0
        (centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) later 0 state)
        boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling (by decide) later 0 boundary)

def cutoffTwoRawBoundaryMoment (later state : Nat) : Q' :=
  listQSum
    (cutoffTwoRawBoundaryMomentTerm later state)
    (centralBoundaryChannels later 0)

theorem cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative
    (later : Nat) (boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling (by decide) later 0 boundary := by
  unfold centralPositiveBoundaryTotalHalfAmplitude
    finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro state _hstate
  exact centralHalfAmplitude_nonnegative
    (by decide) later 0 state boundary

theorem cutoffTwoRawBoundaryMomentTerm_nonnegative
    (later state : Nat) {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels later 0) :
    (0 : Q') ≤ cutoffTwoRawBoundaryMomentTerm later state boundary := by
  unfold cutoffTwoRawBoundaryMomentTerm
  exact Q'.mul_nonneg _ _
    (centralBoundaryWeight_nonnegative_on
      (by decide) boundary hboundary)
    (Q'.mul_nonneg _ _
      (centralHalfAmplitude_nonnegative
        (by decide) later 0 _ boundary)
      (cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative
        later boundary))

/-- Reordering the finite target and boundary sums gives the literal
boundary-message first moment of one raw BF4 row. -/
theorem cutoffTwoRawStationaryRowMass_eqv_boundaryMoment
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoRawStationaryRowMass later state ≈
      cutoffTwoRawBoundaryMoment later state := by
  have hsourcePositive :=
    centralPhysicalFiniteStateAt_mem_positive
      cutoffTwoHalfCoupling (by decide) later 0
      (centralPhysicalFiniteVacuumSectorIndex_lt
        cutoffTwoHalfCoupling (by decide) later 0 hstate)
  have hsourceHalf :=
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
  unfold cutoffTwoRawStationaryRowMass cutoffTwoRawBoundaryMoment
    cutoffTwoRawBoundaryMomentTerm
  refine Q'.eqv_trans _
    (listQSum
      (weightedGram
        (centralBoundaryChannels later 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling later 0)
        (centralHalfAmplitude cutoffTwoHalfCoupling later 0)
        (centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) later 0 state))
      (centralPositiveHalfStates
        cutoffTwoHalfCoupling (by decide) later 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact centralPhysicalReflectedKernel_eq_weightedGram
      cutoffTwoHalfCoupling hsourceHalf
      ((mem_centralPositiveHalfStates_iff.mp htarget).1)
  · exact weightedGram_row_eq_channelTotal
      (centralPositiveHalfStates
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralBoundaryChannels later 0)
      (centralBoundaryWeight cutoffTwoHalfCoupling later 0)
      (centralHalfAmplitude cutoffTwoHalfCoupling later 0)
      (centralPhysicalFiniteStateAt
        cutoffTwoHalfCoupling (by decide) later 0 state)

/-! ## 2. A local half-amplitude Harnack datum -/

/-- A pointwise projective comparison of literal half-slab amplitudes across
every positive physical edge at one cutoff. -/
structure CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt
    (later : Nat) (rho : Q') : Type where
  rho_nonnegative : (0 : Q') ≤ rho
  amplitude_le : ∀ left,
    left ∈ cutoffTwoEdgeLoadFullStates later →
    ∀ right,
      right ∈ cutoffTwoEdgeLoadFullStates later →
      (0 : Q') < cutoffTwoEdgeLoadKernel later left right →
      ∀ boundary,
        boundary ∈ centralBoundaryChannels later 0 →
        centralHalfAmplitude cutoffTwoHalfCoupling later 0
            (centralPhysicalFiniteStateAt
              cutoffTwoHalfCoupling (by decide) later 0 left)
            boundary ≤
          rho *
            centralHalfAmplitude cutoffTwoHalfCoupling later 0
              (centralPhysicalFiniteStateAt
                cutoffTwoHalfCoupling (by decide) later 0 right)
              boundary

private theorem q_boundary_moment_scale_reorder
    (weight rho amplitude total : Q') :
    weight * ((rho * amplitude) * total) ≈
      rho * (weight * (amplitude * total)) := by
  refine Q'.eqv_trans _
    (weight * (rho * (amplitude * total))) _
    (Q'.mul_eqv_congr_left weight _ _
      (Q'.mul_assoc_eqv rho amplitude total)) ?_
  refine Q'.eqv_trans _
    ((weight * rho) * (amplitude * total)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv weight rho (amplitude * total))) ?_
  refine Q'.eqv_trans _
    ((rho * weight) * (amplitude * total)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv weight rho)) ?_
  exact Q'.mul_assoc_eqv rho weight (amplitude * total)

theorem cutoffTwoRawBoundaryMomentTerm_le_rho_mul_of_halfAmplitudeHarnack
    {later : Nat} {rho : Q'}
    (harnack : CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt later rho)
    {left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels later 0) :
    cutoffTwoRawBoundaryMomentTerm later left boundary ≤
      rho * cutoffTwoRawBoundaryMomentTerm later right boundary := by
  have htotal : (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling (by decide) later 0 boundary :=
    cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative later boundary
  have hweight : (0 : Q') ≤
      centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary :=
    centralBoundaryWeight_nonnegative_on
      (by decide) boundary hboundary
  unfold cutoffTwoRawBoundaryMomentTerm
  refine Q'.le_trans' _
    (centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary *
      ((rho *
          centralHalfAmplitude cutoffTwoHalfCoupling later 0
            (centralPhysicalFiniteStateAt
              cutoffTwoHalfCoupling (by decide) later 0 right)
            boundary) *
        centralPositiveBoundaryTotalHalfAmplitude
          cutoffTwoHalfCoupling (by decide) later 0 boundary)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (harnack.amplitude_le
          left hleft right hright hforward boundary hboundary)
        htotal)
      hweight
  · exact Q'.le_of_eqv
      (q_boundary_moment_scale_reorder
        (centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary)
        rho
        (centralHalfAmplitude cutoffTwoHalfCoupling later 0
          (centralPhysicalFiniteStateAt
            cutoffTwoHalfCoupling (by decide) later 0 right)
          boundary)
        (centralPositiveBoundaryTotalHalfAmplitude
          cutoffTwoHalfCoupling (by decide) later 0 boundary))

theorem cutoffTwoRawBoundaryMoment_le_rho_mul_of_halfAmplitudeHarnack
    {later : Nat} {rho : Q'}
    (harnack : CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt later rho)
    {left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    cutoffTwoRawBoundaryMoment later left ≤
      rho * cutoffTwoRawBoundaryMoment later right := by
  unfold cutoffTwoRawBoundaryMoment
  refine Q'.le_trans' _
    (listQSum
      (fun boundary =>
        rho * cutoffTwoRawBoundaryMomentTerm later right boundary)
      (centralBoundaryChannels later 0)) _ ?_ ?_
  · apply listQSum_mono
    intro boundary hboundary
    exact
      cutoffTwoRawBoundaryMomentTerm_le_rho_mul_of_halfAmplitudeHarnack
        harnack hleft hright hforward hboundary
  · exact Q'.le_of_eqv
      (listQSum_mul_left rho
        (cutoffTwoRawBoundaryMomentTerm later right)
        (centralBoundaryChannels later 0))

/-! ## 3. Contraction to the conditional edge ceiling -/

theorem cutoffTwoRawStationaryRowMassRatio_le_of_halfAmplitudeHarnack
    {later : Nat} {rho : Q'}
    (harnack : CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt later rho)
    {left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoRawStationaryRowMass later left)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) ≤
      rho := by
  apply Q'.divPos_le_of_le_mul
  refine Q'.le_trans' _
    (cutoffTwoRawBoundaryMoment later left) _
    (Q'.le_of_eqv
      (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hleft)) ?_
  refine Q'.le_trans' _
    (rho * cutoffTwoRawBoundaryMoment later right) _
    (cutoffTwoRawBoundaryMoment_le_rho_mul_of_halfAmplitudeHarnack
      harnack hleft hright hforward) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left rho _ _
      (Q'.eqv_symm
        (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hright)))

theorem cutoffTwoConditionalReverseForwardRatio_le_of_halfAmplitudeHarnack
    {later : Nat} {rho : Q'}
    (harnack : CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt later rho)
    {left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later right left)
        (cutoffTwoEdgeLoadConditionalKernel later left right)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          hleft hforward) ≤
      rho := by
  refine Q'.le_trans' _
    (Q'.divPos
      (cutoffTwoRawStationaryRowMass later left)
      (cutoffTwoRawStationaryRowMass later right)
      (cutoffTwoRawStationaryRowMass_pos hright)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
            hleft hright hforward))
        (cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio hleft hright))
  · exact cutoffTwoRawStationaryRowMassRatio_le_of_halfAmplitudeHarnack
      harnack hleft hright hforward

namespace CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt

def toConditionalReverseForwardCeilingAt
    {later : Nat} {rho : Q'}
    (harnack : CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt later rho) :
    CutoffTwoConditionalReverseForwardCeilingAt later rho where
  rho_nonnegative := harnack.rho_nonnegative
  ratio_le := fun _left hleft _right hright hforward =>
    cutoffTwoConditionalReverseForwardRatio_le_of_halfAmplitudeHarnack
      harnack hleft hright hforward

end CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt

/-! ## 4. Cofinal Harnack-and-payment compiler -/

structure CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment : Type 1 where
  rho : Q'
  rho_nonnegative : (0 : Q') ≤ rho
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  local_harnack : ∀ request,
    CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt
      (anchor request) rho
  harnack_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalRatioCeilingLoad
            rho (anchor request) source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment

def toCofinalNovelConditionalRatioCeilingBound
    (bound : CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun _request => bound.rho
  local_ceiling := fun request =>
    (bound.local_harnack request).toConditionalReverseForwardCeilingAt
  ceiling_capacity := fun request => bound.harnack_capacity request

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.cutoffTwoRawStationaryRowMass_eqv_boundaryMoment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.cutoffTwoRawBoundaryMomentTerm_le_rho_mul_of_halfAmplitudeHarnack
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.cutoffTwoRawBoundaryMoment_le_rho_mul_of_halfAmplitudeHarnack
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.cutoffTwoRawStationaryRowMassRatio_le_of_halfAmplitudeHarnack
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.cutoffTwoConditionalReverseForwardRatio_le_of_halfAmplitudeHarnack
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt.toConditionalReverseForwardCeilingAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment.toCompletedStrictContractionData
