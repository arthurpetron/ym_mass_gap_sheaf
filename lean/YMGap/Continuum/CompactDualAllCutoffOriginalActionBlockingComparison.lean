/-
# One exact all-cutoff original-action blocking comparison

The lossless retained-intertwiner kernel already pushes the normalized fine
physical Gibbs law to an enriched effective law.  Its forgetting kernel then
recovers the former all-cutoff blocked law exactly.  This module composes those
two concrete kernels on observables and joins the result to the exact coarse
Wilson-law remainder decomposition.

For every rational observable on the coarse physical carrier:

* its two-stage conditional pullback has exactly the same expectation under
  the original normalized fine action as under the induced enriched law;
* forgetting the enriched law gives exactly the old all-cutoff blocked law;
* comparison with the normalized coarse Wilson action leaves precisely the
  already-defined signed pushforward remainder;
* if the observable is pointwise bounded by one, the expectation defect is
  bounded by the literal `L1` norm of that remainder.

Thus no induced interaction is discarded before the explicit forgetting
kernel, and no claim is made that the blocked law remains in the one-parameter
Wilson family.  The result is one finite blocking step.  It does not bound the
remainder along a refining trajectory, make the enriched target into a
repeatable same-object carrier, construct a continuum modulus, or prove a
mass gap.

Constructive contract: finite exact-rational Fubini and existing physical
kernel identities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedProjection
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable

namespace YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingComparison

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4PhysicalMarkovL2Contraction
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedProjection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Observable transport through the explicit forgetting kernel -/

/-- Conditional expectation of a coarse physical observable in one row of
the explicit forgetting kernel.  On a coherent target this evaluates the
observable at that coarse state; on a retained target it keeps the terminal
null-completion law rather than silently deleting the retained sector. -/
def allCutoffRetainedForgetObservablePullback
    (S : SlabScalePair) (observable : EdgeLabelling → Q')
    (retained : AllCutoffRetainedTarget) : Q' :=
  listQSum
    (fun coarseState =>
      allCutoffRetainedForgetKernel S retained coarseState *
        observable coarseState)
    S.coarse.physicalLabellings

/-- The complete observable transported from the coarse physical carrier
back through forgetting and then through the lossless enriched block kernel. -/
def allCutoffOriginalActionObservablePullback
    (S : SlabScalePair) (observable : EdgeLabelling → Q')
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  allCutoffRetainedObservablePullback S
    (allCutoffRetainedForgetObservablePullback S observable) source

/-- Expectation under the former all-cutoff blocked law. -/
def allCutoffOldBlockedExpectation
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q') : Q' :=
  observableExpectation
    (allCutoffPhysicalKernel S hfineCutoff).blockedMass
    S.coarse.physicalLabellings observable

/-- Expectation under the normalized coarse Wilson/BF4 physical action. -/
def allCutoffCoarseWilsonExpectation
    (S : SlabScalePair) (observable : EdgeLabelling → Q') : Q' :=
  observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings observable

/-- The forgetting pullback preserves the constant observable on every listed
enriched target.  This is the second normalization in the two-stage step. -/
theorem allCutoffRetainedForgetObservablePullback_one
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (retained : AllCutoffRetainedTarget)
    (hretained : retained ∈ allCutoffRetainedTargets S) :
    allCutoffRetainedForgetObservablePullback S (fun _ => 1) retained ≈
      1 := by
  unfold allCutoffRetainedForgetObservablePullback
  refine Q'.eqv_trans _
    (listQSum
      (allCutoffRetainedForgetKernel S retained)
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro coarseState _
    exact Q'.mul_one_eqv _
  · exact allCutoffRetainedForgetKernel_row_normalized
      S hfineCutoff hretained

/-- Both stochastic rows together preserve the constant observable. -/
theorem allCutoffOriginalActionObservablePullback_one
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : SlabPhysicalSourceEntry S.fine) :
    allCutoffOriginalActionObservablePullback S (fun _ => 1) source ≈
      1 := by
  unfold allCutoffOriginalActionObservablePullback
    allCutoffRetainedObservablePullback
  refine Q'.eqv_trans _
    (listQSum
      (allCutoffRetainedFineIntertwinerKernel S source)
      (allCutoffRetainedTargets S)) _ ?_ ?_
  · apply listQSum_congr_on
    intro retained hretained
    refine Q'.eqv_trans _
      (allCutoffRetainedFineIntertwinerKernel S source retained * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (allCutoffRetainedForgetObservablePullback_one
          S hfineCutoff retained hretained)
    · exact Q'.mul_one_eqv _
  · exact allCutoffRetainedFineIntertwinerKernel_row_normalized
      S hfineCutoff source

/-! ## 2. Exact original-action to blocked-law identity -/

/-- Pushing the enriched effective law through the explicit forgetting
kernel gives the old blocked expectation for every coarse observable. -/
theorem allCutoffRetainedBlockedExpectation_forget_eqv_oldBlockedExpectation
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q') :
    allCutoffRetainedBlockedExpectation S
        (allCutoffRetainedForgetObservablePullback S observable) ≈
      allCutoffOldBlockedExpectation S hfineCutoff observable := by
  unfold allCutoffRetainedBlockedExpectation
    allCutoffRetainedForgetObservablePullback
    allCutoffOldBlockedExpectation observableExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun retained =>
        listQSum
          (fun coarseState =>
            (allCutoffRetainedFineIntertwinerBlockedMass S retained *
                allCutoffRetainedForgetKernel S retained coarseState) *
              observable coarseState)
          S.coarse.physicalLabellings)
      (allCutoffRetainedTargets S)) _ ?_ ?_
  · apply listQSum_congr_on
    intro retained _
    refine Q'.eqv_trans _
      (listQSum
        (fun coarseState =>
          allCutoffRetainedFineIntertwinerBlockedMass S retained *
            (allCutoffRetainedForgetKernel S retained coarseState *
              observable coarseState))
        S.coarse.physicalLabellings) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_mul_left
          (allCutoffRetainedFineIntertwinerBlockedMass S retained)
          (fun coarseState =>
            allCutoffRetainedForgetKernel S retained coarseState *
              observable coarseState)
          S.coarse.physicalLabellings)
    · apply listQSum_congr_on
      intro coarseState _
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        listQSum
          (fun retained =>
            (allCutoffRetainedFineIntertwinerBlockedMass S retained *
                allCutoffRetainedForgetKernel S retained coarseState) *
              observable coarseState)
          (allCutoffRetainedTargets S))
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun retained coarseState =>
          (allCutoffRetainedFineIntertwinerBlockedMass S retained *
              allCutoffRetainedForgetKernel S retained coarseState) *
            observable coarseState)
        (allCutoffRetainedTargets S)
        S.coarse.physicalLabellings)
  refine Q'.eqv_trans _
    (listQSum
      (fun coarseState =>
        allCutoffRetainedForgottenBlockedMass S coarseState *
          observable coarseState)
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro coarseState _
    exact listQSum_mul_right
      (fun retained =>
        allCutoffRetainedFineIntertwinerBlockedMass S retained *
          allCutoffRetainedForgetKernel S retained coarseState)
      (observable coarseState) (allCutoffRetainedTargets S)
  · apply listQSum_congr_on
    intro coarseState hcoarse
    exact Q'.mul_eqv_congr_right _ _ (observable coarseState)
      (allCutoffRetainedForgottenBlockedMass_eqv_oldBlockedMass
        S hfineCutoff coarseState hcoarse)

/-- Exact finite ORIGINAL-action blocking identity.  The normalized fine
physical expectation of the two-stage observable pullback equals expectation
under the complete induced blocked law after its explicit terminal forgetting
kernel. -/
theorem allCutoffOriginalActionExpectation_eqv_oldBlockedExpectation
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q') :
    allCutoffFinePhysicalExpectation S
        (allCutoffOriginalActionObservablePullback S observable) ≈
      allCutoffOldBlockedExpectation S hfineCutoff observable := by
  exact Q'.eqv_trans _
    (allCutoffRetainedBlockedExpectation S
      (allCutoffRetainedForgetObservablePullback S observable)) _
    (Q'.eqv_symm
      (allCutoffRetainedBlockedExpectation_eqv_pullback S
        (allCutoffRetainedForgetObservablePullback S observable)))
    (allCutoffRetainedBlockedExpectation_forget_eqv_oldBlockedExpectation
      S hfineCutoff observable)

/-! ## 3. Comparison with the coarse Wilson action -/

/-- The complete one-step expectation comparison: original fine action,
lossless induced enriched law, explicit forgetting kernel, and normalized
coarse Wilson action are joined without assuming Wilson-family closure.  The
only residual is the actual signed pushed-law remainder. -/
theorem allCutoffOriginalActionExpectation_eqv_coarseWilson_add_remainder
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q') :
    allCutoffFinePhysicalExpectation S
        (allCutoffOriginalActionObservablePullback S observable) ≈
      allCutoffCoarseWilsonExpectation S observable +
        remainderObservableExpectation
          (allCutoffPhysicalKernel S hfineCutoff) observable := by
  refine Q'.eqv_trans _
    (allCutoffOldBlockedExpectation S hfineCutoff observable) _
    (allCutoffOriginalActionExpectation_eqv_oldBlockedExpectation
      S hfineCutoff observable) ?_
  exact blockedObservableExpectation_eqv_coarse_add_remainder
    (allCutoffPhysicalKernel S hfineCutoff) observable

/-- Subtracting the normalized coarse Wilson expectation leaves exactly the
signed expectation of the physical pushforward remainder. -/
theorem allCutoffOriginalActionExpectation_sub_coarseWilson_eqv_remainder
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q') :
    allCutoffFinePhysicalExpectation S
          (allCutoffOriginalActionObservablePullback S observable) +
        -(allCutoffCoarseWilsonExpectation S observable) ≈
      remainderObservableExpectation
        (allCutoffPhysicalKernel S hfineCutoff) observable := by
  refine Q'.eqv_trans _
    (allCutoffOldBlockedExpectation S hfineCutoff observable +
      -(allCutoffCoarseWilsonExpectation S observable)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (allCutoffOriginalActionExpectation_eqv_oldBlockedExpectation
        S hfineCutoff observable)
  · exact blocked_sub_coarseObservableExpectation_eqv_remainder
      (allCutoffPhysicalKernel S hfineCutoff) observable

/-- Quantitative one-step comparison for any unit-bounded coarse observable.
The bound is the literal total-variation norm of the exact blocked-versus-
coarse-Wilson remainder, with no carrier-cardinality factor. -/
theorem allCutoffOriginalActionExpectation_defect_le_remainderL1
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : EdgeLabelling → Q')
    (hbound : ∀ state, state ∈ S.coarse.physicalLabellings →
      Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (allCutoffFinePhysicalExpectation S
            (allCutoffOriginalActionObservablePullback S observable) +
          -(allCutoffCoarseWilsonExpectation S observable)) ≤
      (allCutoffPhysicalKernel S hfineCutoff).remainderL1 := by
  refine Q'.le_trans' _
    (Q'.abs
      (remainderObservableExpectation
        (allCutoffPhysicalKernel S hfineCutoff) observable)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (allCutoffOriginalActionExpectation_sub_coarseWilson_eqv_remainder
          S hfineCutoff observable))
  · exact remainderObservableExpectation_abs_le_remainderL1
      (allCutoffPhysicalKernel S hfineCutoff) observable hbound

/-! ## Axiom audit -/

#print axioms allCutoffRetainedForgetObservablePullback
#print axioms allCutoffOriginalActionObservablePullback
#print axioms allCutoffRetainedForgetObservablePullback_one
#print axioms allCutoffOriginalActionObservablePullback_one
#print axioms allCutoffRetainedBlockedExpectation_forget_eqv_oldBlockedExpectation
#print axioms allCutoffOriginalActionExpectation_eqv_oldBlockedExpectation
#print axioms allCutoffOriginalActionExpectation_eqv_coarseWilson_add_remainder
#print axioms allCutoffOriginalActionExpectation_sub_coarseWilson_eqv_remainder
#print axioms allCutoffOriginalActionExpectation_defect_le_remainderL1

end YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingComparison
