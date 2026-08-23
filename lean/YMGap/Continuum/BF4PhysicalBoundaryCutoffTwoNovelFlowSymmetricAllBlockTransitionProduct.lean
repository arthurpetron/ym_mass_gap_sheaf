/-
# Exact transition-product form of every symmetric BF4 capacity block

The pathwise transition-product formula used for old-to-new traffic only needs
the selected edge source to lie in the retained carrier.  It therefore applies
unchanged to old--old and new--new edges.  This module exposes that generality
and rewrites all three oriented symmetric capacity fields in one common form:
the average of a source-prefix and a through-edge target-prefix transition
product must fit inside the appropriate conditional transition allocation.

The resulting three-block transition-product certificate is constructively
equivalent to the physical three-field capacity datum.  Exact finite Boolean
scans decide its three fields, and cofinal success compiles to completed strict
contraction.  No scan-success theorem, uniform transition-product bound,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One transition-product load for every retained source -/

def cutoffTwoNovelSymmetricTransitionProductLoad
    (later source target : Nat) : Q' :=
  HalfPow.half *
      cutoffTwoNovelConditionalTransitionProductLoad
        later source target +
    HalfPow.half *
      cutoffTwoNovelConditionalTargetTransitionProductLoad
        later target source

/-- The symmetric relative load has the same exact transition-product
expansion on every retained-source edge, not only on cross edges. -/
theorem cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
        later source target ≈
      cutoffTwoNovelSymmetricTransitionProductLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
    cutoffTwoNovelSymmetricTransitionProductLoad
  apply Q'.add_eqv_congr'
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.eqv_trans _ _ _
        (cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
          hsource target)
        (cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
          later source target))
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.eqv_trans _ _ _
        (cutoffTwoNovelRelativeTargetEdgeLoad_eqv_conditionalTargetHarnackLoad
          hsource target)
        (cutoffTwoNovelConditionalTargetHarnackLoad_eqv_transitionProductLoad
          later target source))

/-! ## 2. A reversible three-block transition-product certificate -/

structure CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt
    (later : Nat) : Type 1 where
  old_old : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later source target ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later source target
  old_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target
  new_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later source target ≤
        cutoffTwoEdgeLoadConditionalKernel later source target

namespace CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt

def toOrientedCapacityAt
    {later : Nat}
    (capacity :
      CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later) :
    CutoffTwoNovelSymmetricOrientedCapacityAt later where
  old_old := by
    intro source hsource target htarget
    let conditional : CutoffTwoNovelSymmetricOldOldConditionalCapacityAt later :=
      { relative_capacity := fun source hsource target htarget => by
          have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
            (List.mem_filter.mp hsource).1
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (Q'.mul_eqv_congr_left
                cutoffTwoNovelSimpleFlowCoercivityFloor _ _
                (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
                  hsourceFull target)))
            (capacity.old_old source hsource target htarget) }
    exact conditional.old_old source hsource target htarget
  old_new := by
    intro source hsource target htarget
    let transition : CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt
        later :=
      { transition_capacity := fun source hsource target htarget => by
          unfold cutoffTwoNovelSymmetricCrossTransitionProductLoad
          exact capacity.old_new source hsource target htarget }
    exact transition.toOldNewConditionalCapacityAt.old_new
      source hsource target htarget
  new_new := by
    intro source hsource target htarget
    let conditional : CutoffTwoNovelSymmetricNewNewConditionalCapacityAt later :=
      { relative_capacity := fun source hsource target htarget => by
          have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
            (List.mem_filter.mp hsource).1
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (Q'.mul_eqv_congr_left
                cutoffTwoNovelSimpleFlowCoercivityFloor _ _
                (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
                  hsourceFull target)))
            (capacity.new_new source hsource target htarget) }
    exact conditional.new_new source hsource target htarget

/-- Every physical three-field certificate can be recovered in exact
transition-product coordinates. -/
def ofOrientedCapacityAt
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later) :
    CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later where
  old_old := by
    intro source hsource target htarget
    have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
      (List.mem_filter.mp hsource).1
    have hrelative :=
      (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
        hsourceFull target).mp
        (capacity.old_old source hsource target htarget)
    have hproduct :
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            cutoffTwoNovelSimpleFlowCoercivityFloor _ _
            (Q'.eqv_symm
              (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
                hsourceFull target))))
        hrelative
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old
          hsource htarget))
  old_new := by
    intro source hsource target htarget
    have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
      (List.mem_filter.mp hsource).1
    have hrelative :=
      (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
        hsourceFull target).mp
        (capacity.old_new source hsource target htarget)
    have hproduct :
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            cutoffTwoNovelSimpleFlowCoercivityFloor _ _
            (Q'.eqv_symm
              (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
                hsourceFull target))))
        hrelative
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_old_new
          hsource htarget))
  new_new := by
    intro source hsource target htarget
    have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
      (List.mem_filter.mp hsource).1
    have hrelative :=
      (cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional
        hsourceFull target).mp
        (capacity.new_new source hsource target htarget)
    have hproduct :
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            cutoffTwoNovelSimpleFlowCoercivityFloor _ _
            (Q'.eqv_symm
              (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
                hsourceFull target))))
        hrelative
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_new_new
          hsource htarget))

end CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt

/-! ## 3. Three exact finite transition-product scans -/

def cutoffTwoNovelSymmetricOldOldTransitionProductCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later pair.1 pair.2 ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

def cutoffTwoNovelSymmetricOldNewTransitionProductCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

def cutoffTwoNovelSymmetricNewNewTransitionProductCapacityCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

def cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck
    (later : Nat) : Bool :=
  cutoffTwoNovelSymmetricOldOldTransitionProductCapacityCheck later &&
    (cutoffTwoNovelSymmetricOldNewTransitionProductCapacityCheck later &&
      cutoffTwoNovelSymmetricNewNewTransitionProductCapacityCheck later)

def cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt_of_check
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck
        later = true) :
    CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later := by
  have houter := (Bool.and_eq_true _ _).mp hcheck
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  exact
    { old_old := by
        unfold cutoffTwoNovelSymmetricOldOldTransitionProductCapacityCheck at houter
        intro source hsource target htarget
        exact of_decide_eq_true
          (List.all_eq_true.mp houter.1 (source, target)
            ((mem_cartesian_iff _ _ (source, target)).2
              ⟨hsource, htarget⟩))
      old_new := by
        unfold cutoffTwoNovelSymmetricOldNewTransitionProductCapacityCheck at hinner
        intro source hsource target htarget
        exact of_decide_eq_true
          (List.all_eq_true.mp hinner.1 (source, target)
            ((mem_cartesian_iff _ _ (source, target)).2
              ⟨hsource, htarget⟩))
      new_new := by
        unfold cutoffTwoNovelSymmetricNewNewTransitionProductCapacityCheck at hinner
        intro source hsource target htarget
        exact of_decide_eq_true
          (List.all_eq_true.mp hinner.2 (source, target)
            ((mem_cartesian_iff _ _ (source, target)).2
              ⟨hsource, htarget⟩)) }

theorem cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck_complete
    {later : Nat}
    (capacity :
      CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later) :
    cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck
      later = true := by
  unfold cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · unfold cutoffTwoNovelSymmetricOldOldTransitionProductCapacityCheck
    apply List.all_eq_true.mpr
    intro pair hpair
    have hblocks :=
      (mem_cartesian_iff
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later) pair).1 hpair
    exact decide_eq_true
      (capacity.old_old pair.1 hblocks.1 pair.2 hblocks.2)
  · apply (Bool.and_eq_true _ _).mpr
    constructor
    · unfold cutoffTwoNovelSymmetricOldNewTransitionProductCapacityCheck
      apply List.all_eq_true.mpr
      intro pair hpair
      have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
      exact decide_eq_true
        (capacity.old_new pair.1 hblocks.1 pair.2 hblocks.2)
    · unfold cutoffTwoNovelSymmetricNewNewTransitionProductCapacityCheck
      apply List.all_eq_true.mpr
      intro pair hpair
      have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
      exact decide_eq_true
        (capacity.new_new pair.1 hblocks.1 pair.2 hblocks.2)

/-! ## 4. Cofinal exact transition-product success reaches completion -/

structure CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck :
    Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck

def toCofinalNovelSymmetricOrientedCapacity
    (checked :
      CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck) :
    CutoffTwoCofinalNovelSymmetricOrientedCapacity where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  capacity := fun request =>
    (cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt_of_check
      (checked.anchor request) (checked.check request)).toOrientedCapacityAt

def toCompletedStrictContractionData
    (checked :
      CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt.toOrientedCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt.ofOrientedCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck.toCompletedStrictContractionData
