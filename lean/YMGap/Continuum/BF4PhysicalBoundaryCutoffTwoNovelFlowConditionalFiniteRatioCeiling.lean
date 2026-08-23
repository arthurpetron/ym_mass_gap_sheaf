/-
# The concrete finite conditional-ratio ceiling for cutoff-two novel BF4 flow

Every fixed vacuum-sector carrier is a literal finite list.  This module
totalizes the reverse/forward conditional ratio on all ordered carrier pairs
and takes its located rational maximum.  Every positive physical edge is
therefore bounded by a constructed ceiling, eliminating the local projective
field from the fixed-cutoff flow certificate.

The maximum may grow with the cutoff, and the corresponding ceiling-weighted
path load is not proved uniformly payable.  Thus this is a finite construction
only; no uniform gap, thermodynamic/continuum theory, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Totalized edge ratio and located maximum -/

/-- Reverse/forward conditional ratio on a positive carrier edge, totalized
by zero away from that domain. -/
def cutoffTwoConditionalReverseForwardRatio
    (later left right : Nat) : Q' :=
  if hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if _hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      if hforward : (0 : Q') <
          cutoffTwoEdgeLoadKernel later left right then
        Q'.divPos
          (cutoffTwoEdgeLoadConditionalKernel later right left)
          (cutoffTwoEdgeLoadConditionalKernel later left right)
          (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
            hleft hforward)
      else 0
    else 0
  else 0

theorem cutoffTwoConditionalReverseForwardRatio_nonnegative
    (later left right : Nat) :
    (0 : Q') ≤
      cutoffTwoConditionalReverseForwardRatio later left right := by
  unfold cutoffTwoConditionalReverseForwardRatio
  split
  · split
    · split
      · unfold Q'.divPos
        exact Q'.mul_nonneg _ _
          (cutoffTwoEdgeLoadConditionalKernel_nonnegative
            later right left)
          (Q'.le_of_lt (Q'.recipPos_pos _ _))
      · exact Q'.le_refl' 0
    · exact Q'.le_refl' 0
  · exact Q'.le_refl' 0

/-- Located maximum of all totalized directed conditional ratios on the
literal finite carrier. -/
def cutoffTwoConditionalReverseForwardFiniteCeiling
    (later : Nat) : Q' :=
  listQMaxZero
    (fun pair : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio
        later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))

theorem cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative
    (later : Nat) :
    (0 : Q') ≤
      cutoffTwoConditionalReverseForwardFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardFiniteCeiling
  apply listQMaxZero_nonnegative
  intro pair
  exact cutoffTwoConditionalReverseForwardRatio_nonnegative
    later pair.1 pair.2

theorem cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') <
      cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later right left)
        (cutoffTwoEdgeLoadConditionalKernel later left right)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          hleft hforward) ≤
      cutoffTwoConditionalReverseForwardFiniteCeiling later := by
  have hmember : (left, right) ∈
      cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later) :=
    (mem_cartesian_iff _ _ (left, right)).2 ⟨hleft, hright⟩
  have hmax := le_listQMaxZero_of_mem
    (fun pair : Nat × Nat =>
      cutoffTwoConditionalReverseForwardRatio
        later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))
    hmember
  change cutoffTwoConditionalReverseForwardRatio later left right ≤
    cutoffTwoConditionalReverseForwardFiniteCeiling later at hmax
  unfold cutoffTwoConditionalReverseForwardRatio at hmax
  rw [dif_pos hleft, dif_pos hright, dif_pos hforward] at hmax
  exact hmax

/-! ## 2. Fixed-cutoff ceiling data and concrete load -/

def cutoffTwoConditionalReverseForwardFiniteCeilingData
    (later : Nat) :
    CutoffTwoConditionalReverseForwardCeilingAt later
      (cutoffTwoConditionalReverseForwardFiniteCeiling later) where
  rho_nonnegative :=
    cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative later
  ratio_le := fun _ hleft _ hright hforward =>
    cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
      hleft hright hforward

def cutoffTwoNovelConditionalFiniteRatioCeilingLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelConditionalRatioCeilingLoad
    (cutoffTwoConditionalReverseForwardFiniteCeiling later)
    later source target

theorem cutoffTwoNovelConditionalTransitionProductLoad_le_finiteRatioCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelConditionalTransitionProductLoad later source target ≤
      cutoffTwoNovelConditionalFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelConditionalFiniteRatioCeilingLoad
  exact
    cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
      (cutoffTwoConditionalReverseForwardFiniteCeilingData later)
      source target

/-! ## 3. The remaining concrete cofinal counting certificate -/

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_finiteRatioCeiling
    (later : Nat)
    (hceiling : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalFiniteRatioCeilingLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    (cutoffTwoConditionalReverseForwardFiniteCeilingData later)
  exact hceiling

structure CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  ceiling_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelConditionalFiniteRatioCeilingLoad
          (anchor request) source target ≤
      cutoffTwoNovelAllocatedConditionalKernel
        (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound

def toCofinalNovelConditionalRatioCeilingBound
    (bound : CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun request =>
    cutoffTwoConditionalReverseForwardFiniteCeiling
      (bound.anchor request)
  local_ceiling := fun request =>
    cutoffTwoConditionalReverseForwardFiniteCeilingData
      (bound.anchor request)
  ceiling_capacity := fun request => bound.ceiling_capacity request

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling.cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling.cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling.cutoffTwoNovelConditionalTransitionProductLoad_le_finiteRatioCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling.CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound.toCompletedStrictContractionData
