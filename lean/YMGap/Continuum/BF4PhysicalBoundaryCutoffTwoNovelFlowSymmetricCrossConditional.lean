/-
# Old-to-new conditional reduction for the symmetric cutoff-two novel flow

Symmetrizing the directed novel-flow load removes the need to pay a separate
new-to-old capacity field.  This module shows that it also removes the
stationary-mass-ratio obstruction on a cross edge.  For an old source `s` and
a new target `t`, divide the forward load `L(s,t)` by the source weight and
the reverse load `L(t,s)` by its target weight.  Both denominators are then
the same old stationary weight `weight(s)`, so

  weight(s) * symmetricRelativeLoad(s,t) = symmetricLoad(s,t).

The allocated conditional kernel on an old-to-new edge is the full
conditional transition (the half allocation applies only to old--old edges).
Consequently the physical cross-capacity inequality is exactly equivalent to
a ratio-free conditional inequality based at the old source.

The final structure is a genuine `Type`-level certificate for that remaining
conditional inequality.  It is not inhabited here.  No uniform cross-edge or
new--new estimate, thermodynamic/continuum construction, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem mul_swap_middle_eqv_local (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-! ## 1. Normalize reverse traffic by its old target -/

/-- A directed novel-flow load divided by the stationary mass of its target.
It is totalized by zero away from the retained finite vacuum sector. -/
def cutoffTwoNovelRelativeTargetEdgeLoad
    (later source target : Nat) : Q' :=
  if htarget : target ∈ cutoffTwoEdgeLoadFullStates later then
    Q'.divPos
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      (cutoffTwoEdgeLoadWeight later target)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) htarget)
  else 0

/-- Multiplication by a retained target's stationary mass exactly recovers
the directed edge load. -/
theorem cutoffTwoEdgeLoadWeight_mul_relativeTargetEdgeLoad_eqv_load
    {later target : Nat}
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later)
    (source : Nat) :
    cutoffTwoEdgeLoadWeight later target *
        cutoffTwoNovelRelativeTargetEdgeLoad later source target ≈
      cutoffTwoNovelSimpleEdgeLoad later source target := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w := cutoffTwoHalfCoupling) (hw := by decide) htarget
  unfold cutoffTwoNovelRelativeTargetEdgeLoad
  rw [dif_pos htarget]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (cutoffTwoEdgeLoadWeight later target)
      (Q'.divPos
        (cutoffTwoNovelSimpleEdgeLoad later source target)
        (cutoffTwoEdgeLoadWeight later target) hweight))
    (Q'.divPos_mul_eqv _ _ hweight)

/-! ## 2. One old source weight factors the symmetric cross load -/

/-- Symmetric relative traffic based at `source`: the forward load is divided
by its source mass and the reverse load by its target mass.  Both are the
stationary mass of `source`. -/
def cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
    (later source target : Nat) : Q' :=
  HalfPow.half *
      cutoffTwoNovelRelativeSourceEdgeLoad later source target +
    HalfPow.half *
      cutoffTwoNovelRelativeTargetEdgeLoad later target source

/-- Exact common-old-weight factorization of the symmetric edge load. -/
theorem cutoffTwoEdgeLoadWeight_mul_symmetricRelativeSourceEdgeLoad_eqv_load
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoEdgeLoadWeight later source *
        cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
          later source target ≈
      cutoffTwoNovelSymmetricEdgeLoad later source target := by
  unfold cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
    cutoffTwoNovelSymmetricEdgeLoad
  refine Q'.eqv_trans _
    (cutoffTwoEdgeLoadWeight later source *
          (HalfPow.half *
            cutoffTwoNovelRelativeSourceEdgeLoad later source target) +
      cutoffTwoEdgeLoadWeight later source *
          (HalfPow.half *
            cutoffTwoNovelRelativeTargetEdgeLoad later target source)) _
    (Q'.mul_add_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (HalfPow.half *
          (cutoffTwoEdgeLoadWeight later source *
            cutoffTwoNovelRelativeSourceEdgeLoad later source target) +
      HalfPow.half *
          (cutoffTwoEdgeLoadWeight later source *
            cutoffTwoNovelRelativeTargetEdgeLoad later target source)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_swap_middle_eqv_local
        (cutoffTwoEdgeLoadWeight later source) HalfPow.half
        (cutoffTwoNovelRelativeSourceEdgeLoad later source target))
      (mul_swap_middle_eqv_local
        (cutoffTwoEdgeLoadWeight later source) HalfPow.half
        (cutoffTwoNovelRelativeTargetEdgeLoad later target source))
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (cutoffTwoEdgeLoadWeight_mul_relativeSourceEdgeLoad_eqv_load
          hsource target))
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (cutoffTwoEdgeLoadWeight_mul_relativeTargetEdgeLoad_eqv_load
          hsource target))

private theorem le_iff_of_eqv_positive_common_left_local
    {weight left right reducedLeft reducedRight : Q'}
    (hweight : (0 : Q') < weight)
    (hleft : left ≈ weight * reducedLeft)
    (hright : right ≈ weight * reducedRight) :
    left ≤ right ↔ reducedLeft ≤ reducedRight := by
  constructor
  · intro h
    have hscaled : weight * reducedLeft ≤ weight * reducedRight :=
      Q'.le_trans' _ left _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ right _ h (Q'.le_of_eqv hright))
    exact Q'.le_of_mul_le_mul_left hscaled hweight
  · intro h
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      reducedLeft reducedRight weight h (Q'.le_of_lt hweight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-! ## 3. Exact cross-capacity cancellation -/

/-- Symmetric physical capacity is exactly a conditional inequality after
cancelling the common retained source weight. -/
theorem cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target) ↔
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w := cutoffTwoHalfCoupling) (hw := by decide) hsource
  have hloadFactor :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≈
        cutoffTwoEdgeLoadWeight later source *
          (cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
              later source target) := by
    refine Q'.eqv_trans _
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
        (cutoffTwoEdgeLoadWeight later source *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later source target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (Q'.eqv_symm
          (cutoffTwoEdgeLoadWeight_mul_symmetricRelativeSourceEdgeLoad_eqv_load
            hsource target))
    · exact mul_swap_middle_eqv_local
        cutoffTwoNovelSimpleFlowCoercivityFloor
        (cutoffTwoEdgeLoadWeight later source)
        (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
          later source target)
  exact le_iff_of_eqv_positive_common_left_local hweight hloadFactor
    (cutoffTwoNovelAllocatedKernel_eqv_weight_mul_conditional
      hsource target)

/-- The old--old half allocation is absent on an old-to-new edge, so its
allocated conditional capacity is the whole conditional transition. -/
theorem cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_old_new
    {later source target : Nat}
    (_hsource : source ∈ cutoffTwoEdgeLoadOldStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadNewStates later) :
    cutoffTwoNovelAllocatedConditionalKernel later source target ≈
      cutoffTwoEdgeLoadConditionalKernel later source target := by
  have htargetNotOld : target ∉ cutoffTwoEdgeLoadOldStates later := by
    intro htargetOld
    unfold cutoffTwoEdgeLoadOldStates at htargetOld
    unfold cutoffTwoEdgeLoadNewStates at htarget
    have holdDecision := (List.mem_filter.mp htargetOld).2
    have hnewDecision := (List.mem_filter.mp htarget).2
    simp only [holdDecision, Bool.not_true] at hnewDecision
    exact Bool.noConfusion hnewDecision
  unfold cutoffTwoNovelAllocatedConditionalKernel
    cutoffTwoNovelAllocationFraction
  rw [dif_neg (fun h => htargetNotOld h.2)]
  exact Q'.one_mul_eqv _

/-- A non-vacuous Type-level witness for the remaining ratio-free old-to-new
conditional estimate. -/
structure CutoffTwoNovelSymmetricOldNewConditionalCapacityAt
    (later : Nat) : Type 1 where
  relative_capacity : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target

namespace CutoffTwoNovelSymmetricOldNewConditionalCapacityAt

/-- The ratio-free conditional certificate supplies exactly the `old_new`
field required by the symmetric three-field compiler. -/
theorem old_new
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later)
    (source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadOldStates later)
    (target : Nat)
    (htarget : target ∈ cutoffTwoEdgeLoadNewStates later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricEdgeLoad later source target ≤
      cutoffTwoNovelAllocatedKernel later source target := by
  have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hsource).1
  apply
    (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
      hsourceFull target).mpr
  exact Q'.le_trans' _ _ _
    (capacity.relative_capacity source hsource target htarget)
    (Q'.ge_of_eqv
      (cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_old_new
        hsource htarget))

end CutoffTwoNovelSymmetricOldNewConditionalCapacityAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.cutoffTwoEdgeLoadWeight_mul_relativeTargetEdgeLoad_eqv_load
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.cutoffTwoEdgeLoadWeight_mul_symmetricRelativeSourceEdgeLoad_eqv_load
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_old_new
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.CutoffTwoNovelSymmetricOldNewConditionalCapacityAt.old_new
