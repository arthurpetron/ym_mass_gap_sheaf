/-
# Conditional normalization of the symmetric BF4 diagonal blocks

The exact three-block checker still states its diagonal comparisons in joint
stationary form.  This module cancels the positive stationary source weight on
old--old and new--new edges.  The old--old allocation becomes one half of the
conditional transition, while the new--new allocation becomes the full
conditional transition.

The normalized diagonal checks are proved Boolean-equal to the preceding
physical checks.  Replacing both diagonal scans by their conditional versions
therefore leaves the combined three-block decision unchanged, and a cofinal
successful normalized schedule compiles to completed strict contraction.

No check-success theorem, uniform congestion estimate, thermodynamic/continuum
construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact allocation factors on both diagonal blocks -/

theorem cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old
    {later source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadOldStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadOldStates later) :
    cutoffTwoNovelAllocatedConditionalKernel later source target ≈
      HalfPow.half *
        cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelAllocatedConditionalKernel
    cutoffTwoNovelAllocationFraction
  rw [dif_pos ⟨hsource, htarget⟩]
  exact Q'.eqv_refl _

private theorem cutoffTwoNewState_not_old_local
    {later state : Nat}
    (hnew : state ∈ cutoffTwoEdgeLoadNewStates later) :
    state ∉ cutoffTwoEdgeLoadOldStates later := by
  intro hold
  unfold cutoffTwoEdgeLoadOldStates at hold
  unfold cutoffTwoEdgeLoadNewStates at hnew
  have holdDecision := (List.mem_filter.mp hold).2
  have hnewDecision := (List.mem_filter.mp hnew).2
  simp only [holdDecision, Bool.not_true] at hnewDecision
  exact Bool.noConfusion hnewDecision

theorem cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_new_new
    {later source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadNewStates later)
    (_htarget : target ∈ cutoffTwoEdgeLoadNewStates later) :
    cutoffTwoNovelAllocatedConditionalKernel later source target ≈
      cutoffTwoEdgeLoadConditionalKernel later source target := by
  have hsourceNotOld := cutoffTwoNewState_not_old_local hsource
  unfold cutoffTwoNovelAllocatedConditionalKernel
    cutoffTwoNovelAllocationFraction
  rw [dif_neg (fun h => hsourceNotOld h.1)]
  exact Q'.one_mul_eqv _

/-! ## 2. Conditional certificates reproduce both physical fields -/

structure CutoffTwoNovelSymmetricOldOldConditionalCapacityAt
    (later : Nat) : Type 1 where
  relative_capacity : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later source target ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later source target

namespace CutoffTwoNovelSymmetricOldOldConditionalCapacityAt

theorem old_old
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldOldConditionalCapacityAt later)
    (source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadOldStates later)
    (target : Nat)
    (htarget : target ∈ cutoffTwoEdgeLoadOldStates later) :
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
      (cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old
        hsource htarget))

end CutoffTwoNovelSymmetricOldOldConditionalCapacityAt

structure CutoffTwoNovelSymmetricNewNewConditionalCapacityAt
    (later : Nat) : Type 1 where
  relative_capacity : ∀ source,
    source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target

namespace CutoffTwoNovelSymmetricNewNewConditionalCapacityAt

theorem new_new
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricNewNewConditionalCapacityAt later)
    (source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadNewStates later)
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
      (cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_new_new
        hsource htarget))

end CutoffTwoNovelSymmetricNewNewConditionalCapacityAt

/-! ## 3. Exact conditional diagonal scans -/

def cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later pair.1 pair.2 ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

def cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck later = true) :
    CutoffTwoNovelSymmetricOldOldConditionalCapacityAt later where
  relative_capacity := by
    unfold cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck at hcheck
    intro source hsource target htarget
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck (source, target)
        ((mem_cartesian_iff _ _ (source, target)).2
          ⟨hsource, htarget⟩))

theorem cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_complete
    (later : Nat)
    (capacity : CutoffTwoNovelSymmetricOldOldConditionalCapacityAt later) :
    cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck later = true := by
  unfold cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hblocks :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later) pair).1 hpair
  exact decide_eq_true
    (capacity.relative_capacity pair.1 hblocks.1 pair.2 hblocks.2)

def cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

def cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck later = true) :
    CutoffTwoNovelSymmetricNewNewConditionalCapacityAt later where
  relative_capacity := by
    unfold cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck at hcheck
    intro source hsource target htarget
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck (source, target)
        ((mem_cartesian_iff _ _ (source, target)).2
          ⟨hsource, htarget⟩))

theorem cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_complete
    (later : Nat)
    (capacity : CutoffTwoNovelSymmetricNewNewConditionalCapacityAt later) :
    cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck later = true := by
  unfold cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hblocks :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
  exact decide_eq_true
    (capacity.relative_capacity pair.1 hblocks.1 pair.2 hblocks.2)

/-! ## 4. Boolean equality with the physical diagonal scans -/

theorem cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_eq_physical
    (later : Nat) :
    cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck later =
      cutoffTwoNovelSymmetricOldOldCapacityCheck later := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hconditional
    apply cutoffTwoNovelSymmetricOldOldCapacityCheck_complete
    exact
      (cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_sound
        later hconditional).old_old
  · intro hphysical
    apply cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_complete
    refine { relative_capacity := ?_ }
    intro source hsource target htarget
    have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
      (List.mem_filter.mp hsource).1
    have hphysicalAt :=
      cutoffTwoNovelSymmetricOldOldCapacityCheck_sound
        later hphysical source hsource target htarget
    have hconditionalAt :=
      (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
        hsourceFull target).mp hphysicalAt
    exact Q'.le_trans' _ _ _ hconditionalAt
      (Q'.le_of_eqv
        (cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old
          hsource htarget))

theorem cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_eq_physical
    (later : Nat) :
    cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck later =
      cutoffTwoNovelSymmetricNewNewCapacityCheck later := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hconditional
    apply cutoffTwoNovelSymmetricNewNewCapacityCheck_complete
    exact
      (cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_sound
        later hconditional).new_new
  · intro hphysical
    apply cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_complete
    refine { relative_capacity := ?_ }
    intro source hsource target htarget
    have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
      (List.mem_filter.mp hsource).1
    have hphysicalAt :=
      cutoffTwoNovelSymmetricNewNewCapacityCheck_sound
        later hphysical source hsource target htarget
    have hconditionalAt :=
      (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
        hsourceFull target).mp hphysicalAt
    exact Q'.le_trans' _ _ _ hconditionalAt
      (Q'.le_of_eqv
        (cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_new_new
          hsource htarget))

/-! ## 5. The normalized three-block checker and completed compiler -/

def cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck
    (later : Nat) : Bool :=
  cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck later &&
    (cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later &&
      cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck later)

theorem cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck_eq_physical
    (later : Nat) :
    cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck later =
      cutoffTwoNovelSymmetricThreeBlockCapacityCheck later := by
  unfold cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck
    cutoffTwoNovelSymmetricThreeBlockCapacityCheck
  rw [cutoffTwoNovelSymmetricOldOldConditionalCapacityCheck_eq_physical,
    cutoffTwoNovelSymmetricNewNewConditionalCapacityCheck_eq_physical]

structure CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck

def toCofinalNovelSymmetricThreeBlockCheck
    (checked : CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck) :
    CutoffTwoCofinalNovelSymmetricThreeBlockCheck where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  check := fun request => by
    rw [← cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck_eq_physical]
    exact checked.check request

def toCompletedStrictContractionData
    (checked : CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalNovelSymmetricThreeBlockCheck.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.CutoffTwoNovelSymmetricOldOldConditionalCapacityAt.old_old
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.CutoffTwoNovelSymmetricNewNewConditionalCapacityAt.new_new
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck_eq_physical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck.toCompletedStrictContractionData
