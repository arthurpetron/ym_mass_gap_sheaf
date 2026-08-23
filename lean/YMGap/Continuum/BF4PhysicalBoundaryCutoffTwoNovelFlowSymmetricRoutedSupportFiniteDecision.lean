/-
# Finite all-block decision using only actual routed support

The carrier-wide ratio ceiling can be inflated by edges that no canonical
novel path uses.  This module substitutes the routed-support maximum into the
common symmetric ceiling load and decides its payment separately on old--old,
old-to-new, and new--new edges.

Success constructs exact physical capacity through the routed-ceiling
compiler.  Failure returns a literal failed edge tagged by block.  No scan is
claimed to succeed, and no cofinal estimate, thermodynamic/continuum
construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Routed-support load and three exact scans -/

def cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelSymmetricRoutedRatioCeilingLoad
    (cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later)
    later source target

theorem cutoffTwoNovelSymmetricTransitionProductLoad_le_routedSupportFiniteCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelSymmetricTransitionProductLoad later source target ≤
      cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
    (cutoffTwoNovelRoutedSupportFiniteRatioCeilingData later)
    source target

def cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck later =
        true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadOldStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          HalfPow.half *
            cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck at hcheck
  intro source hsource target htarget
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target)
      ((mem_cartesian_iff _ _ (source, target)).2
        ⟨hsource, htarget⟩))

def cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck later =
        true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck at hcheck
  intro source hsource target htarget
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target)
      ((mem_cartesian_iff _ _ (source, target)).2
        ⟨hsource, htarget⟩))

def cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck later =
        true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadNewStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck at hcheck
  intro source hsource target htarget
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target)
      ((mem_cartesian_iff _ _ (source, target)).2
        ⟨hsource, htarget⟩))

/-! ## 2. Combined success certificate -/

def cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck
    (later : Nat) : Bool :=
  cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck later &&
    (cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck later &&
      cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck later)

def cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_routedSupportCheck
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck later =
        true) :
    CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later := by
  have houter := (Bool.and_eq_true _ _).mp hcheck
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  exact
    { rho := cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later
      routed_ceiling :=
        cutoffTwoNovelRoutedSupportFiniteRatioCeilingData later
      old_old :=
        cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck_sound
          later houter.1
      old_new :=
        cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck_sound
          later hinner.1
      new_new :=
        cutoffTwoNovelSymmetricNewNewRoutedSupportFiniteCeilingCheck_sound
          later hinner.2 }

/-! ## 3. Certificate or literal failed routed-ceiling edge -/

inductive CutoffTwoNovelSymmetricRoutedSupportFiniteCeilingOutcome
    (later : Nat) : Type 1
  | certified
      (capacity :
        CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later)
  | overloadedOldOldEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadOldStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          HalfPow.half *
            cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedOldNewEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedNewNewEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadNewStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)

def inspectCutoffTwoNovelSymmetricRoutedSupportFiniteCeiling
    (later : Nat) :
    CutoffTwoNovelSymmetricRoutedSupportFiniteCeilingOutcome later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
            later pair.1 pair.2)
      (fun pair : Nat × Nat =>
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
      (cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later)) with
  | failed pair hpair hfailure =>
      have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
      exact .overloadedOldOldEdge
        pair.1 pair.2 hblocks.1 hblocks.2 hfailure
  | certified hold =>
      cases inspectListComparison
          (fun pair : Nat × Nat =>
            cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
                later pair.1 pair.2)
          (fun pair : Nat × Nat =>
            cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
          (cartesian
            (cutoffTwoEdgeLoadOldStates later)
            (cutoffTwoEdgeLoadNewStates later)) with
      | failed pair hpair hfailure =>
          have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
          exact .overloadedOldNewEdge
            pair.1 pair.2 hblocks.1 hblocks.2 hfailure
      | certified hcross =>
          cases inspectListComparison
              (fun pair : Nat × Nat =>
                cutoffTwoNovelSimpleFlowCoercivityFloor *
                  cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad
                    later pair.1 pair.2)
              (fun pair : Nat × Nat =>
                cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
              (cartesian
                (cutoffTwoEdgeLoadNewStates later)
                (cutoffTwoEdgeLoadNewStates later)) with
          | failed pair hpair hfailure =>
              have hblocks := (mem_cartesian_iff _ _ pair).1 hpair
              exact .overloadedNewNewEdge
                pair.1 pair.2 hblocks.1 hblocks.2 hfailure
          | certified hnew =>
              apply
                CutoffTwoNovelSymmetricRoutedSupportFiniteCeilingOutcome.certified
              exact
                { rho :=
                    cutoffTwoConditionalReverseForwardRoutedFiniteCeiling later
                  routed_ceiling :=
                    cutoffTwoNovelRoutedSupportFiniteRatioCeilingData later
                  old_old := fun source hsource target htarget =>
                    hold (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩)
                  old_new := fun source hsource target htarget =>
                    hcross (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩)
                  new_new := fun source hsource target htarget =>
                    hnew (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩) }

/-! ## 4. Cofinal routed-support checks reach completion -/

structure CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck :
    Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck

def toCofinalRoutedCeilingCapacity
    (checked :
      CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck) :
    CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  capacity := fun request =>
    cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_routedSupportCheck
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked :
      CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalRoutedCeilingCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricTransitionProductLoad_le_routedSupportFiniteCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricOldOldRoutedSupportFiniteCeilingCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricOldNewRoutedSupportFiniteCeilingCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_routedSupportCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.inspectCutoffTwoNovelSymmetricRoutedSupportFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.CutoffTwoCofinalNovelSymmetricRoutedSupportFiniteCeilingCheck.toCompletedStrictContractionData
