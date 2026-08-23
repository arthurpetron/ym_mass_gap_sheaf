/-
# Finite all-block decision for the common symmetric routed ceiling

At every cutoff, the constructively located maximum of reverse/forward
conditional ratios supplies the common routed-prefix ceiling.  This module
checks payment of its symmetric ceiling load on old--old, old-to-new, and
new--new edges.  Success constructs the full three-block routed-ceiling
certificate and hence exact physical capacity.

Constructive inspection returns either that certificate or a literal failed
ceiling-payment edge tagged by block.  Failure diagnoses this conservative
majorant and does not by itself refute the smaller exact transition-product
load.

No cofinal scan success, uniform estimate, thermodynamic/continuum
construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Concrete common ceiling and its exact diagonal scans -/

def cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
    later source target

theorem cutoffTwoNovelSymmetricTransitionProductLoad_le_finiteCeilingLoad
    (later source target : Nat) :
    cutoffTwoNovelSymmetricTransitionProductLoad
        later source target ≤
      cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
        later source target := by
  unfold cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
    cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad
    (cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData later)
    source target

def cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck later = true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadOldStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
              later source target ≤
          HalfPow.half *
            cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck at hcheck
  intro source hsource target htarget
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target)
      ((mem_cartesian_iff _ _ (source, target)).2
        ⟨hsource, htarget⟩))

def cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck later = true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadNewStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck at hcheck
  intro source hsource target htarget
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target)
      ((mem_cartesian_iff _ _ (source, target)).2
        ⟨hsource, htarget⟩))

/-! ## 2. One finite sufficient check for all three blocks -/

def cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck
    (later : Nat) : Bool :=
  cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck later &&
    (cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later &&
      cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck later)

def cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_finiteCheck
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck later = true) :
    CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later := by
  have houter := (Bool.and_eq_true _ _).mp hcheck
  have hinner := (Bool.and_eq_true _ _).mp houter.2
  exact
    { rho := cutoffTwoConditionalReverseForwardFiniteCeiling later
      routed_ceiling := cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData later
      old_old := by
        intro source hsource target htarget
        exact cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck_sound
          later houter.1 source hsource target htarget
      old_new := by
        intro source hsource target htarget
        exact cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_sound
          later hinner.1 source hsource target htarget
      new_new := by
        intro source hsource target htarget
        exact cutoffTwoNovelSymmetricNewNewFiniteRatioCeilingCheck_sound
          later hinner.2 source hsource target htarget }

/-! ## 3. Certificate or literal failed ceiling edge -/

inductive CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome
    (later : Nat) : Type 1
  | certified
      (capacity :
        CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt later)
  | overloadedOldOldCeilingEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadOldStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
              later source target ≤
          HalfPow.half *
            cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedOldNewCeilingEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedNewNewCeilingEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadNewStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)

def inspectCutoffTwoNovelSymmetricAllBlockFiniteRatioCeiling
    (later : Nat) :
    CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
            later pair.1 pair.2)
      (fun pair : Nat × Nat =>
        HalfPow.half *
          cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
      (cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later)) with
  | failed pair hpair hfailure =>
      have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadOldStates later) pair).1 hpair
      exact
        CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome.overloadedOldOldCeilingEdge
          pair.1 pair.2 hblocks.1 hblocks.2 hfailure
  | certified hold =>
      cases inspectListComparison
          (fun pair : Nat × Nat =>
            cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
                later pair.1 pair.2)
          (fun pair : Nat × Nat =>
            cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
          (cartesian
            (cutoffTwoEdgeLoadOldStates later)
            (cutoffTwoEdgeLoadNewStates later)) with
      | failed pair hpair hfailure =>
          have hblocks :=
            (mem_cartesian_iff
              (cutoffTwoEdgeLoadOldStates later)
              (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
          exact
            CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome.overloadedOldNewCeilingEdge
              pair.1 pair.2 hblocks.1 hblocks.2 hfailure
      | certified hcross =>
          cases inspectListComparison
              (fun pair : Nat × Nat =>
                cutoffTwoNovelSimpleFlowCoercivityFloor *
                  cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad
                    later pair.1 pair.2)
              (fun pair : Nat × Nat =>
                cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
              (cartesian
                (cutoffTwoEdgeLoadNewStates later)
                (cutoffTwoEdgeLoadNewStates later)) with
          | failed pair hpair hfailure =>
              have hblocks :=
                (mem_cartesian_iff
                  (cutoffTwoEdgeLoadNewStates later)
                  (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
              exact
                CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome.overloadedNewNewCeilingEdge
                  pair.1 pair.2 hblocks.1 hblocks.2 hfailure
          | certified hnew =>
              apply
                CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome.certified
              exact
                { rho := cutoffTwoConditionalReverseForwardFiniteCeiling later
                  routed_ceiling :=
                    cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData later
                  old_old := fun source hsource target htarget => by
                    exact hold (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩)
                  old_new := fun source hsource target htarget => by
                    exact hcross (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩)
                  new_new := fun source hsource target htarget => by
                    exact hnew (source, target)
                      ((mem_cartesian_iff _ _ (source, target)).2
                        ⟨hsource, htarget⟩) }

/-! ## 4. Cofinal finite ceiling checks reach completion -/

structure CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck :
    Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck

def toCofinalRoutedCeilingCapacity
    (checked :
      CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck) :
    CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  capacity := fun request =>
    cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_finiteCheck
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked :
      CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalRoutedCeilingCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.cutoffTwoNovelSymmetricTransitionProductLoad_le_finiteCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.cutoffTwoNovelSymmetricOldOldFiniteRatioCeilingCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_finiteCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.inspectCutoffTwoNovelSymmetricAllBlockFiniteRatioCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.CutoffTwoCofinalNovelSymmetricAllBlockFiniteRatioCeilingCheck.toCompletedStrictContractionData
