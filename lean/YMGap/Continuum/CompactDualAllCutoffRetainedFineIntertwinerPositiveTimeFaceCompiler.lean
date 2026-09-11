/-
# Positive-time face compiler on the retained all-cutoff branch

An enriched target has two physical coordinate systems: the coarse summand
and the retained fine summand.  This module chooses one lower-half face in
each system and defines the corresponding branch-explicit target observable.
The reflected target observable is obtained from the geometrically reflected
face in each system, and enriched target reflection exchanges the two exactly.

On every positive incoherent source row, the retained kernel does not alter
the physical fine state.  Consequently the enriched root observable pulls
back to the existing lower-half face observable, and the enriched reflected
observable pulls back to that same observable evaluated on the reflected
upper restriction.  This is an exact same-object positive-time
identification on precisely the retained rows introduced to repair the
all-cutoff carrier failure.

The coherent source branch still contains a genuine coarse recoupling
expectation.  Thus this module does not claim a whole-law OS identity,
reflection positivity of the enriched law, a time-transfer gap, or a
continuum theorem.

## Axiom gate

Boolean face evaluation, exact kernel event transport, and the existing
physical lower/upper restriction identities only.  No classical choice,
placeholder, trusted external computation, computability escape, heartbeat
increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
import YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A lower-face choice at both block scales -/

/-- One positive-time face coordinate in each physical branch of an enriched
block target. -/
structure EnrichedLowerFaceGeometry (S : SlabScalePair) : Type where
  fineRoot : Nat
  coarseRoot : Nat
  fineRoot_lower : fineRoot ∈ centralLowerFaceIds S.fine.half
  coarseRoot_lower : coarseRoot ∈ centralLowerFaceIds S.coarse.half

namespace EnrichedLowerFaceGeometry

def fineReflected {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) : Nat :=
  slabFaceReflectId S.fine.extent G.fineRoot

def coarseReflected {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) : Nat :=
  slabFaceReflectId S.coarse.extent G.coarseRoot

theorem fineRoot_mem {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) :
    G.fineRoot ∈ slabPhysicalFaceEdges S.fine.extent := by
  simpa only [SlabPhysicalData.extent] using
    (mem_centralLowerFaceIds.mp G.fineRoot_lower).1

theorem coarseRoot_mem {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) :
    G.coarseRoot ∈ slabPhysicalFaceEdges S.coarse.extent := by
  simpa only [SlabPhysicalData.extent] using
    (mem_centralLowerFaceIds.mp G.coarseRoot_lower).1

theorem fineReflected_mem {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) :
    G.fineReflected ∈ slabPhysicalFaceEdges S.fine.extent :=
  slabFaceReflectId_physical G.fineRoot_mem

theorem coarseReflected_mem {S : SlabScalePair}
    (G : EnrichedLowerFaceGeometry S) :
    G.coarseReflected ∈ slabPhysicalFaceEdges S.coarse.extent :=
  slabFaceReflectId_physical G.coarseRoot_mem

end EnrichedLowerFaceGeometry

/-! ## 2. Root and reflected observables on the enriched carrier -/

def enrichedLowerFaceObservable
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S) :
    AllCutoffRetainedTarget → Q' :=
  allCutoffRetainedBranchEventIndicator
    (slabPhysicalFacePositiveB G.fineRoot)
    (slabPhysicalFacePositiveB G.coarseRoot)

def enrichedReflectedFaceObservable
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S) :
    AllCutoffRetainedTarget → Q' :=
  allCutoffRetainedBranchEventIndicator
    (slabPhysicalFacePositiveB G.fineReflected)
    (slabPhysicalFacePositiveB G.coarseReflected)

private theorem facePositive_reflection
    (D : SlabPhysicalData) (root : Nat)
    (hroot : root ∈ slabPhysicalFaceEdges D.extent)
    (physical : EdgeLabelling) :
    slabPhysicalFacePositiveB root (D.reflectLabelling physical) =
    slabPhysicalFacePositiveB
        (slabFaceReflectId D.extent root) physical := by
  simp [slabPhysicalFacePositiveB, SlabPhysicalData.reflectLabelling,
    reflectSupportedSlabFaceLabelling, hroot]

/-- Enriched reflection sends the lower-face observable to the matching
reflected-face observable in both the coarse and retained summands. -/
theorem enrichedLowerFaceObservable_reflection
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (target : AllCutoffRetainedTarget) :
    enrichedLowerFaceObservable G
        (reflectAllCutoffRetainedTarget S target) =
      enrichedReflectedFaceObservable G target := by
  cases target with
  | inl coarseState =>
      change rationalBoolIndicator
          (slabPhysicalFacePositiveB G.coarseRoot
            (S.coarse.reflectLabelling coarseState)) =
        rationalBoolIndicator
          (slabPhysicalFacePositiveB G.coarseReflected coarseState)
      rw [facePositive_reflection S.coarse G.coarseRoot G.coarseRoot_mem]
      rfl
  | inr retained =>
      change rationalBoolIndicator
          (slabPhysicalFacePositiveB G.fineRoot
            (S.fine.reflectLabelling retained.1)) =
        rationalBoolIndicator
          (slabPhysicalFacePositiveB G.fineReflected retained.1)
      rw [facePositive_reflection S.fine G.fineRoot G.fineRoot_mem]
      rfl

/-- Observable pullback respects the same lower-to-reflected-face exchange. -/
theorem enrichedLowerFacePullback_reflection
    {S : SlabScalePair} (hfineCutoff : 1 ≤ S.fine.cutoff)
    (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G)
        (reflectSlabPhysicalSourceEntry source) ≈
      allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source := by
  refine Q'.eqv_trans _
    (allCutoffRetainedObservablePullback S
      (fun target =>
        enrichedLowerFaceObservable G
          (reflectAllCutoffRetainedTarget S target)) source) _
    (allCutoffRetainedObservablePullback_reflection
      S hfineCutoff (enrichedLowerFaceObservable G) source) ?_
  unfold allCutoffRetainedObservablePullback
  apply listQSum_congr_on _ _ (allCutoffRetainedTargets S)
  intro target _
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_of_eq (enrichedLowerFaceObservable_reflection G target)

/-! ## 3. Exact retained-row same-object identification -/

theorem enrichedLowerFacePullback_eqv_fineIndicator_of_incoherent
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G) source ≈
      rationalBoolIndicator
        (slabPhysicalFacePositiveB G.fineRoot source.1) := by
  exact
    allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
      S source hpositive hnotPartition
      (slabPhysicalFacePositiveB G.fineRoot)
      (slabPhysicalFacePositiveB G.coarseRoot)

/-- On a retained row, the enriched root observable is literally the existing
positive-time lower-half face observable. -/
theorem enrichedLowerFacePullback_eqv_lowerPositiveTime_of_incoherent
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G) source ≈
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
        (centralLowerRestriction S.fine.half source.1) := by
  refine Q'.eqv_trans _
    (rationalBoolIndicator
      (slabPhysicalFacePositiveB G.fineRoot source.1)) _
    (enrichedLowerFacePullback_eqv_fineIndicator_of_incoherent
      G source hpositive hnotPartition) ?_
  exact Q'.eqv_of_eq
    (slabPhysicalFacePositiveUnitObservable_lowerRestriction
      G.fineRoot_lower source.1).symm

/-- On the same retained row, the reflected enriched observable is literally
the same positive-time face observable evaluated on the reflected upper
restriction. -/
theorem enrichedReflectedFacePullback_eqv_upperPositiveTime_of_incoherent
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source ≈
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
        (centralReflectedUpperRestriction S.fine.half source.1) := by
  refine Q'.eqv_trans _
    (rationalBoolIndicator
      (slabPhysicalFacePositiveB G.fineReflected source.1)) _ ?_ ?_
  · exact
      allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
        S source hpositive hnotPartition
        (slabPhysicalFacePositiveB G.fineReflected)
        (slabPhysicalFacePositiveB G.coarseReflected)
  · exact Q'.eqv_of_eq
      (slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
        G.fineRoot_lower source.1).symm

/-! ## Axiom audit -/

#print axioms EnrichedLowerFaceGeometry.fineReflected_mem
#print axioms enrichedLowerFaceObservable_reflection
#print axioms enrichedLowerFacePullback_reflection
#print axioms enrichedLowerFacePullback_eqv_lowerPositiveTime_of_incoherent
#print axioms enrichedReflectedFacePullback_eqv_upperPositiveTime_of_incoherent

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
