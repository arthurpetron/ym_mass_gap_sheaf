/-
# Observable pullback through the lossless all-cutoff block kernel

The enriched stochastic kernel is now normalized and reflection covariant,
and its pushed target law is known exactly.  This module turns those facts
into the observable-side compiler needed for a causal same-object route.

For every rational observable on the disjoint enriched target, its pullback is
the literal conditional expectation in one kernel row.  Finite Fubini proves
that target expectation under the pushed law equals source expectation of the
pullback.  Target and source reflection commute with this compiler.  Finally,
rowwise finite Jensen and the exact pushforward identity prove that pullback is
a contraction between the corresponding finite weighted `L2` seminorms.

This is a spatial block-map contraction between two different finite carriers,
not an Osterwalder--Schrader time-transfer operator.  A later positive-time
half-amplitude identification must show that the relevant target observables
and reflected joint law are carried by the existing physical half-slab Gram.

## Axiom gate

Finite Fubini, exact rational algebra, and finite square Jensen only.  No
classical choice, placeholder, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPushedReflection
import YMGap.Continuum.BF4PhysicalMarkovL2Contraction

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalMarkovL2Contraction
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPushedReflection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Generic finite Fubini compiler -/

private theorem finitePushedExpectation_eqv_pullback
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (sourceMass : Source → Q') (kernel : Source → Target → Q')
    (observable : Target → Q') :
    listQSum
        (fun target =>
          listQSum
              (fun source => sourceMass source * kernel source target)
              sources *
            observable target)
        targets ≈
      listQSum
        (fun source =>
          sourceMass source *
            listQSum
              (fun target => kernel source target * observable target)
              targets)
        sources := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            (sourceMass source * kernel source target) * observable target)
          sources)
      targets) _ ?_ ?_
  · apply listQSum_congr_on _ _ targets
    intro target _
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun source => sourceMass source * kernel source target)
        (observable target) sources)
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (sourceMass source * kernel source target) * observable target)
          targets)
      sources) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun target source =>
          (sourceMass source * kernel source target) * observable target)
        targets sources)
  · apply listQSum_congr_on _ _ sources
    intro source _
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          sourceMass source *
            (kernel source target * observable target))
        targets) _ ?_ ?_
    · apply listQSum_congr_on _ _ targets
      intro target _
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left
        (sourceMass source)
        (fun target => kernel source target * observable target)
        targets

/-! ## 1. The observable compiler and its expectations -/

/-- Conditional expectation of an enriched target observable in one physical
source row. -/
def allCutoffRetainedObservablePullback
    (S : SlabScalePair)
    (observable : AllCutoffRetainedTarget → Q')
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  listQSum
    (fun target =>
      allCutoffRetainedFineIntertwinerKernel S source target *
        observable target)
    (allCutoffRetainedTargets S)

/-- Expectation on the fine physical source carrier. -/
def allCutoffFinePhysicalExpectation
    (S : SlabScalePair)
    (observable : SlabPhysicalSourceEntry S.fine → Q') : Q' :=
  listQSum
    (fun source => S.fine.normalizedMass source.1 * observable source)
    (slabPhysicalSourceEntries S.fine)

/-- Expectation on the disjoint enriched carrier under the exact pushed law. -/
def allCutoffRetainedBlockedExpectation
    (S : SlabScalePair)
    (observable : AllCutoffRetainedTarget → Q') : Q' :=
  listQSum
    (fun target =>
      allCutoffRetainedFineIntertwinerBlockedMass S target *
        observable target)
    (allCutoffRetainedTargets S)

/-- Finite Fubini: the expectation of every target observable under the
pushed law is the fine physical expectation of its literal kernel pullback. -/
theorem allCutoffRetainedBlockedExpectation_eqv_pullback
    (S : SlabScalePair)
    (observable : AllCutoffRetainedTarget → Q') :
    allCutoffRetainedBlockedExpectation S observable ≈
      allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S observable) := by
  unfold allCutoffRetainedBlockedExpectation
    allCutoffRetainedFineIntertwinerBlockedMass
    allCutoffFinePhysicalExpectation
    allCutoffRetainedObservablePullback
  exact finitePushedExpectation_eqv_pullback
    (slabPhysicalSourceEntries S.fine)
    (allCutoffRetainedTargets S)
    (fun source : SlabPhysicalSourceEntry S.fine =>
      S.fine.normalizedMass source.1)
    (allCutoffRetainedFineIntertwinerKernel S)
    observable

theorem allCutoffRetainedObservablePullback_one
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : SlabPhysicalSourceEntry S.fine) :
    allCutoffRetainedObservablePullback S (fun _ => 1) source ≈ 1 := by
  unfold allCutoffRetainedObservablePullback
  refine Q'.eqv_trans _
    (listQSum
      (allCutoffRetainedFineIntertwinerKernel S source)
      (allCutoffRetainedTargets S)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (allCutoffRetainedTargets S)
    intro target _
    exact Q'.mul_one_eqv _
  · exact allCutoffRetainedFineIntertwinerKernel_row_normalized
      S hfineCutoff source

/-! ## 2. Reflection commutes with observable pullback -/

/-- Reflecting the source before pullback is the same as reflecting the target
observable before pullback.  This is the observable-side intertwining law. -/
theorem allCutoffRetainedObservablePullback_reflection
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : AllCutoffRetainedTarget → Q')
    (source : SlabPhysicalSourceEntry S.fine) :
    allCutoffRetainedObservablePullback S observable
        (reflectSlabPhysicalSourceEntry source) ≈
      allCutoffRetainedObservablePullback S
        (fun target =>
          observable (reflectAllCutoffRetainedTarget S target)) source := by
  let reflectedWeight : AllCutoffRetainedTarget → Q' :=
    fun target =>
      allCutoffRetainedFineIntertwinerKernel S
          (reflectSlabPhysicalSourceEntry source) target *
        observable target
  let sourceWeight : AllCutoffRetainedTarget → Q' :=
    fun target =>
      allCutoffRetainedFineIntertwinerKernel S source target *
        observable (reflectAllCutoffRetainedTarget S target)
  unfold allCutoffRetainedObservablePullback
  change listQSum reflectedWeight (allCutoffRetainedTargets S) ≈
    listQSum sourceWeight (allCutoffRetainedTargets S)
  refine Q'.eqv_trans _
    (listQSum reflectedWeight
      ((allCutoffRetainedTargets S).map
        (reflectAllCutoffRetainedTarget S))) _ ?_ ?_
  · exact listQSum_perm reflectedWeight
      (allCutoffRetainedTargets_reflection_perm S).symm
  · rw [listQSum_map]
    apply listQSum_congr_on _ _ (allCutoffRetainedTargets S)
    intro target htarget
    exact Q'.mul_eqv_congr_right _ _ _
      (allCutoffRetainedFineIntertwinerKernel_reflection
        S hfineCutoff source target htarget)

/-! ## 3. Exact finite cross-carrier `L2` contraction -/

def allCutoffFinePhysicalSquaredNorm
    (S : SlabScalePair)
    (observable : SlabPhysicalSourceEntry S.fine → Q') : Q' :=
  allCutoffFinePhysicalExpectation S
    (fun source => observable source * observable source)

def allCutoffRetainedBlockedSquaredNorm
    (S : SlabScalePair)
    (observable : AllCutoffRetainedTarget → Q') : Q' :=
  allCutoffRetainedBlockedExpectation S
    (fun target => observable target * observable target)

/-- The block observable compiler is nonexpansive from target `L2` to source
`L2`.  This is a cross-carrier spatial statement; it is not a spectral bound
for the OS time-transfer operator. -/
theorem allCutoffRetainedObservablePullback_l2_contraction
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (observable : AllCutoffRetainedTarget → Q') :
    allCutoffFinePhysicalSquaredNorm S
        (allCutoffRetainedObservablePullback S observable) ≤
      allCutoffRetainedBlockedSquaredNorm S observable := by
  let squared : AllCutoffRetainedTarget → Q' :=
    fun target => observable target * observable target
  have hrows :
      allCutoffFinePhysicalSquaredNorm S
          (allCutoffRetainedObservablePullback S observable) ≤
        allCutoffFinePhysicalExpectation S
          (allCutoffRetainedObservablePullback S squared) := by
    unfold allCutoffFinePhysicalSquaredNorm
      allCutoffFinePhysicalExpectation
    apply listQSum_mono
    intro source _
    apply Q'.mul_le_mul_of_nonneg_left
    · exact finiteProbabilityRow_square_jensen
        (allCutoffRetainedTargets S)
        (allCutoffRetainedFineIntertwinerKernel S source)
        observable
        (fun target _ =>
          allCutoffRetainedFineIntertwinerKernel_nonnegative
            S source target)
        (allCutoffRetainedFineIntertwinerKernel_row_normalized
          S hfineCutoff source)
    · exact S.fine.normalizedMass_nonnegative source.1
  exact Q'.le_trans' _ _ _ hrows
    (Q'.ge_of_eqv
      (allCutoffRetainedBlockedExpectation_eqv_pullback
        S squared))

/-! ## Axiom audit -/

#print axioms allCutoffRetainedBlockedExpectation_eqv_pullback
#print axioms allCutoffRetainedObservablePullback_one
#print axioms allCutoffRetainedObservablePullback_reflection
#print axioms allCutoffRetainedObservablePullback_l2_contraction

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
