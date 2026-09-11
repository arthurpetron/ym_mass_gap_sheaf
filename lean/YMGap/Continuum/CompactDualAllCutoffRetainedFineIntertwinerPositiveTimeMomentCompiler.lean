/-
# Positive-time moment compiler for the enriched all-cutoff kernel

The retained positive-time face compiler identifies the root and reflected
one-face observables on every positive incoherent row.  An OS or connected
same-object statement also needs their joint moment, and the coherent branch
must be displayed rather than hidden behind the total kernel.

This module therefore compiles the complete root/reflected/joint moment
triple.  On an incoherent positive row the joint pullback is exactly the
product of one literal lower-half face observable and the same observable on
the reflected upper restriction.  On a coherent positive row all three
pullbacks are exactly the corresponding expectations in the genuine
whole-slab recoupling row.  The resulting three absolute defects state,
without an estimate, the precise obstruction to identifying the coherent
row with the fine same-object positive-time moments.

Reflection exchanges the coherent root and reflected moments exactly.  No
positivity or smallness of any coherent defect is asserted here.  In
particular this module does not claim enriched OS positivity, a transfer
operator gap, a cutoff-tower limit, or a continuum theorem.

## Axiom gate

Finite exact-rational event algebra and the preceding branchwise transport
identities only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem rationalBoolIndicator_and_local (left right : Bool) :
    rationalBoolIndicator (left && right) ≈
      rationalBoolIndicator left * rationalBoolIndicator right := by
  cases left <;> cases right <;> decide

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. The reflected joint observable -/

/-- The joint root/reflected-face event on both branches of the enriched
target carrier. -/
def enrichedLowerReflectedFaceObservable
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S) :
    AllCutoffRetainedTarget → Q' :=
  allCutoffRetainedBranchEventIndicator
    (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

/-- The joint Boolean event is exactly the product of the root and reflected
zero-one observables on either enriched branch. -/
theorem enrichedLowerReflectedFaceObservable_eqv_product
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (target : AllCutoffRetainedTarget) :
    enrichedLowerReflectedFaceObservable G target ≈
      enrichedLowerFaceObservable G target *
        enrichedReflectedFaceObservable G target := by
  cases target with
  | inl coarseState =>
      exact rationalBoolIndicator_and_local _ _
  | inr retained =>
      exact rationalBoolIndicator_and_local _ _

/-! ## 2. The coherent recoupling moment triple -/

/-- Expectation of one coarse physical event in the normalized whole-slab
recoupling row selected by a positive raw partition. -/
def coherentRecouplingEventMoment
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseEvent : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fun coarseState =>
      wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition) coarseState *
        rationalBoolIndicator (coarseEvent coarseState))
    S.coarse.physicalLabellings

def coherentLowerFaceMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentRecouplingEventMoment S source hpartition
    (slabPhysicalFacePositiveB G.coarseRoot)

def coherentReflectedFaceMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentRecouplingEventMoment S source hpartition
    (slabPhysicalFacePositiveB G.coarseReflected)

def coherentLowerReflectedFaceMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentRecouplingEventMoment S source hpartition
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

/-- On a coherent row, the enriched root pullback is precisely the coarse
recoupling root moment. -/
theorem enrichedLowerFacePullback_eqv_coherentMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G) source ≈
      coherentLowerFaceMoment G source hpartition := by
  exact
    allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
      S source hpositive hpartition
      (slabPhysicalFacePositiveB G.fineRoot)
      (slabPhysicalFacePositiveB G.coarseRoot)

/-- On the same coherent row, the reflected enriched pullback is precisely
the reflected coarse recoupling moment. -/
theorem enrichedReflectedFacePullback_eqv_coherentMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source ≈
      coherentReflectedFaceMoment G source hpartition := by
  exact
    allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
      S source hpositive hpartition
      (slabPhysicalFacePositiveB G.fineReflected)
      (slabPhysicalFacePositiveB G.coarseReflected)

/-- On a coherent row, the enriched reflected joint pullback is precisely
the joint coarse recoupling moment. -/
theorem enrichedLowerReflectedFacePullback_eqv_coherentMoment
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerReflectedFaceObservable G) source ≈
      coherentLowerReflectedFaceMoment G source hpartition := by
  exact
    allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
      S source hpositive hpartition
      (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
      (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

/-! ## 3. The retained joint moment is one fine same-object product -/

private theorem finePairIndicator_eqv_positiveTimeProduct
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (physical : EdgeLabelling) :
    rationalBoolIndicator
        (slabPhysicalFacePairPositiveB
          G.fineRoot G.fineReflected physical) ≈
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralLowerRestriction S.fine.half physical) *
        (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralReflectedUpperRestriction S.fine.half physical) := by
  refine Q'.eqv_trans _
    (rationalBoolIndicator
        (slabPhysicalFacePositiveB G.fineRoot physical) *
      rationalBoolIndicator
        (slabPhysicalFacePositiveB G.fineReflected physical)) _ ?_ ?_
  · exact rationalBoolIndicator_and_local _ _
  · exact mul_eqv_both_local
      (Q'.eqv_of_eq
        (slabPhysicalFacePositiveUnitObservable_lowerRestriction
          G.fineRoot_lower physical).symm)
      (Q'.eqv_of_eq
        (slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
          G.fineRoot_lower physical).symm)

/-- On an incoherent positive row, the enriched reflected joint observable
is exactly the product of the same fine face observable on the lower and
reflected-upper restrictions. -/
theorem enrichedLowerReflectedFacePullback_eqv_positiveTimeProduct_of_incoherent
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerReflectedFaceObservable G) source ≈
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralLowerRestriction S.fine.half source.1) *
        (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralReflectedUpperRestriction S.fine.half source.1) := by
  refine Q'.eqv_trans _
    (rationalBoolIndicator
      (slabPhysicalFacePairPositiveB
        G.fineRoot G.fineReflected source.1)) _ ?_ ?_
  · exact
      allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
        S source hpositive hnotPartition
        (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
        (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)
  · exact finePairIndicator_eqv_positiveTimeProduct G source.1

/-! ## 4. Reflection and the exact coherent obstruction -/

/-- Coherent row reflection exchanges the coarse root and reflected moments.
The proof uses the already-established total-kernel observable intertwiner,
so it does not depend on a presentation of the recoupling witness. -/
theorem coherentLowerFaceMoment_reflection
    {S : SlabScalePair} (hfineCutoff : 1 ≤ S.fine.cutoff)
    (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    coherentLowerFaceMoment G
        (reflectSlabPhysicalSourceEntry source)
        ((wholeSlabRawRowPartition_reflection_pos_iff
          S source.1).mpr hpartition) ≈
      coherentReflectedFaceMoment G source hpartition := by
  have hreflectedPositive :
      (0 : Q') < S.fine.physicalTerm
        (S.fine.reflectLabelling source.1) :=
    (physicalTerm_reflection_positive_iff S.fine source.2).mpr
      hpositive
  refine Q'.eqv_trans _
    (allCutoffRetainedObservablePullback S
      (enrichedLowerFaceObservable G)
      (reflectSlabPhysicalSourceEntry source)) _ ?_ ?_
  · exact Q'.eqv_symm
      (enrichedLowerFacePullback_eqv_coherentMoment
        G (reflectSlabPhysicalSourceEntry source)
        hreflectedPositive
        ((wholeSlabRawRowPartition_reflection_pos_iff
          S source.1).mpr hpartition))
  · exact Q'.eqv_trans _
      (allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source) _
      (enrichedLowerFacePullback_reflection
        hfineCutoff G source)
      (enrichedReflectedFacePullback_eqv_coherentMoment
        G source hpositive hpartition)

/-- Absolute mismatch between the coherent coarse root moment and the fine
lower-half face value on the same source row. -/
def coherentLowerPositiveTimeDefect
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  Q'.abs
    (coherentLowerFaceMoment G source hpartition -
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
        (centralLowerRestriction S.fine.half source.1))

/-- Absolute mismatch between the coherent coarse reflected moment and the
fine reflected-upper face value on the same source row. -/
def coherentReflectedPositiveTimeDefect
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  Q'.abs
    (coherentReflectedFaceMoment G source hpartition -
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
        (centralReflectedUpperRestriction S.fine.half source.1))

/-- Absolute mismatch between the coherent coarse joint moment and the fine
same-object lower/reflected-upper product on the same source row. -/
def coherentLowerReflectedPositiveTimeDefect
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  Q'.abs
    (coherentLowerReflectedFaceMoment G source hpartition -
      (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralLowerRestriction S.fine.half source.1) *
        (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralReflectedUpperRestriction S.fine.half source.1))

theorem coherentLowerPositiveTimeDefect_eqv_pullback
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    Q'.abs
        (allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G) source -
          (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
            (centralLowerRestriction S.fine.half source.1)) ≈
      coherentLowerPositiveTimeDefect G source hpartition := by
  apply Q'.abs_eqv_congr
  exact Q'.add_eqv_congr'
    (enrichedLowerFacePullback_eqv_coherentMoment
      G source hpositive hpartition)
    (Q'.eqv_refl _)

theorem coherentReflectedPositiveTimeDefect_eqv_pullback
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    Q'.abs
        (allCutoffRetainedObservablePullback S
            (enrichedReflectedFaceObservable G) source -
          (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
            (centralReflectedUpperRestriction S.fine.half source.1)) ≈
      coherentReflectedPositiveTimeDefect G source hpartition := by
  apply Q'.abs_eqv_congr
  exact Q'.add_eqv_congr'
    (enrichedReflectedFacePullback_eqv_coherentMoment
      G source hpositive hpartition)
    (Q'.eqv_refl _)

theorem coherentLowerReflectedPositiveTimeDefect_eqv_pullback
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    Q'.abs
        (allCutoffRetainedObservablePullback S
            (enrichedLowerReflectedFaceObservable G) source -
          (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
              (centralLowerRestriction S.fine.half source.1) *
            (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
              (centralReflectedUpperRestriction S.fine.half source.1)) ≈
      coherentLowerReflectedPositiveTimeDefect G source hpartition := by
  apply Q'.abs_eqv_congr
  exact Q'.add_eqv_congr'
    (enrichedLowerReflectedFacePullback_eqv_coherentMoment
      G source hpositive hpartition)
    (Q'.eqv_refl _)

/-! ## Axiom audit -/

#print axioms enrichedLowerReflectedFaceObservable_eqv_product
#print axioms enrichedLowerFacePullback_eqv_coherentMoment
#print axioms enrichedLowerReflectedFacePullback_eqv_coherentMoment
#print axioms enrichedLowerReflectedFacePullback_eqv_positiveTimeProduct_of_incoherent
#print axioms coherentLowerFaceMoment_reflection
#print axioms coherentLowerReflectedPositiveTimeDefect_eqv_pullback

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
