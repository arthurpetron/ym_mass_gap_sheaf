/-
# Exact finite decision for symmetric old-to-new BF4 capacity

At every fixed cutoff, the existing located maximum constructs a concrete
reverse/forward conditional-ratio ceiling.  This module transports it to the
weaker routed-prefix interface and specializes the resulting symmetric ceiling
load to old-to-new edges only.

A Boolean scan decides exactly whether those finitely many cross edges are
paid by their conditional transitions.  Success returns the old-to-new
capacity certificate consumed by the symmetric compiler.  Constructive
inspection returns either that certificate or a literal overloaded old-to-new
edge for this sufficient ceiling condition.

No scan is claimed to succeed, and failure of the conservative ceiling test is
not failure of the exact flow.  No uniform capacity estimate,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Concrete finite routed ceiling -/

def cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
    (later oldState newState : Nat) : Q' :=
  cutoffTwoNovelSymmetricCrossRatioCeilingLoad
    (cutoffTwoConditionalReverseForwardFiniteCeiling later)
    later oldState newState

def cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData
    (later : Nat) :
    CutoffTwoNovelRoutedPrefixRatioCeilingAt later
      (cutoffTwoConditionalReverseForwardFiniteCeiling later) :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling.CutoffTwoConditionalReverseForwardCeilingAt.toRoutedPrefixRatioCeilingAt
    (cutoffTwoConditionalReverseForwardFiniteCeilingData later)

theorem cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_finiteRatioCeilingLoad
    (later oldState newState : Nat) :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.cutoffTwoNovelSymmetricCrossTransitionProductLoad
        later oldState newState ≤
      cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
        later oldState newState := by
  unfold cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
  exact cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_routedCeilingLoad
    (cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData later)
    oldState newState

/-! ## 2. Exact Boolean scan of only the old-to-new block -/

def cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2))

theorem cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_sound
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later = true) :
    ∀ oldState,
      oldState ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ newState,
        newState ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
              later oldState newState ≤
          cutoffTwoEdgeLoadConditionalKernel
            later oldState newState := by
  unfold cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck at hcheck
  intro oldState hold newState hnew
  have hpair : (oldState, newState) ∈
      cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadNewStates later) :=
    (mem_cartesian_iff _ _ (oldState, newState)).2 ⟨hold, hnew⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (oldState, newState) hpair)

theorem cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_complete
    (later : Nat)
    (hcapacity : ∀ oldState,
      oldState ∈ cutoffTwoEdgeLoadOldStates later →
      ∀ newState,
        newState ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
              later oldState newState ≤
          cutoffTwoEdgeLoadConditionalKernel later oldState newState) :
    cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later = true := by
  unfold cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hblocks :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
  apply decide_eq_true
  exact hcapacity pair.1 hblocks.1 pair.2 hblocks.2

/-- A successful finite cross scan constructs the routed ceiling/payment datum
without any additional analytic field. -/
def cutoffTwoNovelSymmetricOldNewRoutedCeilingCapacityAt_of_check
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later = true) :
    CutoffTwoNovelSymmetricOldNewRoutedCeilingCapacityAt later where
  rho := cutoffTwoConditionalReverseForwardFiniteCeiling later
  routed_ceiling := cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData later
  ceiling_capacity :=
    cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_sound later hcheck

/-- Therefore a successful cross-only scan supplies the exact old-to-new
conditional capacity certificate. -/
def cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check
    (later : Nat)
    (hcheck :
      cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck later = true) :
    CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later :=
  (cutoffTwoNovelSymmetricOldNewRoutedCeilingCapacityAt_of_check
    later hcheck).toTransitionProductCapacityAt.toOldNewConditionalCapacityAt

/-! ## 3. Constructive certificate-or-overloaded-cross-edge inspection -/

inductive CutoffTwoNovelSymmetricCrossFiniteRatioCeilingOutcome
    (later : Nat) : Type 1
  | certified
      (capacity : CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later)
  | overloadedCeilingEdge
      (oldState newState : Nat)
      (old_mem : oldState ∈ cutoffTwoEdgeLoadOldStates later)
      (new_mem : newState ∈ cutoffTwoEdgeLoadNewStates later)
      (not_ceiling_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
              later oldState newState ≤
          cutoffTwoEdgeLoadConditionalKernel later oldState newState)

/-- Decide the finite sufficient cross payment, retaining a literal failed
old-to-new edge when it does not hold. -/
def inspectCutoffTwoNovelSymmetricCrossFiniteRatioCeiling
    (later : Nat) :
    CutoffTwoNovelSymmetricCrossFiniteRatioCeilingOutcome later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad
            later pair.1 pair.2)
      (fun pair : Nat × Nat =>
        cutoffTwoEdgeLoadConditionalKernel later pair.1 pair.2)
      (cartesian
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadNewStates later)) with
  | certified hall =>
      apply CutoffTwoNovelSymmetricCrossFiniteRatioCeilingOutcome.certified
      apply cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check
      apply cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_complete
      intro oldState hold newState hnew
      exact hall (oldState, newState)
        ((mem_cartesian_iff _ _ (oldState, newState)).2 ⟨hold, hnew⟩)
  | failed pair hpair hfailure =>
      have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadNewStates later) pair).1 hpair
      exact
        CutoffTwoNovelSymmetricCrossFiniteRatioCeilingOutcome.overloadedCeilingEdge
          pair.1 pair.2 hblocks.1 hblocks.2 hfailure

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_finiteRatioCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.inspectCutoffTwoNovelSymmetricCrossFiniteRatioCeiling
