/-
# Constructive exact inspection of all symmetric transition-product blocks

The common transition-product checker has three exact finite components.  This
module inspects them sequentially and retains the first failed edge as
Type-level data.  Success returns the full transition-product capacity
certificate; failure records the block, endpoints, membership witnesses, and
negation of the actual transition-product payment.

Because the transition-product certificate is constructively equivalent to
physical symmetric capacity, these failures are exact diagnostics, unlike a
failure of the earlier conservative cross-ceiling test.

No check is claimed to succeed, and no uniform estimate,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProductDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct
open YMGap.Continuum.FiniteWeightedCartesianInjection

inductive CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome
    (later : Nat) : Type 1
  | certified
      (capacity :
        CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt later)
  | overloadedOldOldEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadOldStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          HalfPow.half *
            cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedOldNewEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadOldStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)
  | overloadedNewNewEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadNewStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadNewStates later)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSymmetricTransitionProductLoad
              later source target ≤
          cutoffTwoEdgeLoadConditionalKernel later source target)

/-- Decide the exact three-block transition-product payment, preserving the
first literal overloaded edge when the full certificate is unavailable. -/
def inspectCutoffTwoNovelSymmetricThreeBlockTransitionProductCapacity
    (later : Nat) :
    CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome
      later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricTransitionProductLoad
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
        CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome.overloadedOldOldEdge
          pair.1 pair.2 hblocks.1 hblocks.2 hfailure
  | certified hold =>
      cases inspectListComparison
          (fun pair : Nat × Nat =>
            cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelSymmetricTransitionProductLoad
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
            CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome.overloadedOldNewEdge
              pair.1 pair.2 hblocks.1 hblocks.2 hfailure
      | certified hcross =>
          cases inspectListComparison
              (fun pair : Nat × Nat =>
                cutoffTwoNovelSimpleFlowCoercivityFloor *
                  cutoffTwoNovelSymmetricTransitionProductLoad
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
                CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome.overloadedNewNewEdge
                  pair.1 pair.2 hblocks.1 hblocks.2 hfailure
          | certified hnew =>
              apply
                CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome.certified
              exact
                { old_old := fun source hsource target htarget =>
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

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProductDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProductDecision.inspectCutoffTwoNovelSymmetricThreeBlockTransitionProductCapacity
