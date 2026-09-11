/-
# Complement recoding of the positive-time mismatch envelope

For Boolean events, the mismatch predicate is invariant under complementing
both the fine and coarse events.  Hence the exact raw mismatch average for a
positive-spin face can be bounded using the occupations of the complementary
zero-spin events.  This repairs the obvious weakness of bounding a mismatch
between two highly occupied events by the sum of those high occupations.

The lower, reflected, and joint enriched positive-time defects are therefore
bounded by canonical fine-Gibbs and enriched-pushed probabilities of the
complementary events.  For the joint event the complement means "at least one
of the two faces is zero", exactly as Boolean logic requires.

No rarity estimate is asserted here.  Showing that these complementary event
masses are small with explicit SU(2), coupling, cutoff, volume, and
lattice-spacing dependence is the next analytic obligation.  This module
does not claim reflection positivity, a transfer gap, a cutoff-tower limit,
or a continuum theorem.

## Axiom gate

Boolean case analysis, finite exact-rational event sums, and previously
checked inequalities only.  No classical choice, placeholder, trusted
external computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeComplementEnvelope

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

def booleanComplementEvent
    (event : EdgeLabelling → Bool) (state : EdgeLabelling) : Bool :=
  !(event state)

/-! ## 1. Exact complement invariance -/

theorem cylinderPullbackMismatchEvent_complement
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source target : EdgeLabelling) :
    cylinderPullbackMismatchEvent
        (booleanComplementEvent fineEvent)
        (booleanComplementEvent coarseEvent) source target =
      cylinderPullbackMismatchEvent
        fineEvent coarseEvent source target := by
  unfold cylinderPullbackMismatchEvent booleanComplementEvent
  cases hfine : fineEvent source <;>
    cases hcoarse : coarseEvent target <;>
    simp only [Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true]

/-- Complementing both events leaves the selected raw mismatch numerator and
therefore its normalized ratio unchanged. -/
theorem coherentSelectedRawMismatchRatio_complement
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentSelectedRawMismatchRatio S source hpartition
        (booleanComplementEvent fineEvent)
        (booleanComplementEvent coarseEvent) ≈
      coherentSelectedRawMismatchRatio S source hpartition
        fineEvent coarseEvent := by
  unfold coherentSelectedRawMismatchRatio
    wholeSlabRecouplingRawCylinderRatio Q'.divPos
  apply Q'.mul_eqv_congr_right
  unfold wholeSlabRecouplingRawCylinderMass finiteEventMass
  apply listQSum_congr_on
  intro target _
  rw [cylinderPullbackMismatchEvent_complement]
  exact Q'.eqv_refl _

/-- The complete normalized coherent mismatch average is complement
invariant, with no source- or carrier-dependent factor. -/
theorem coherentEventRawMismatchAverage_complement
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentEventRawMismatchAverage S
        (booleanComplementEvent fineEvent)
        (booleanComplementEvent coarseEvent) ≈
      coherentEventRawMismatchAverage S fineEvent coarseEvent := by
  unfold coherentEventRawMismatchAverage
  apply positiveCoherentWeightedDefect_congr
  intro source hpartition
  exact coherentSelectedRawMismatchRatio_complement
    S source hpartition fineEvent coarseEvent

/-! ## 2. Use complementary occupations to control the same mismatch -/

def complementFinePushedOccupationEnvelope
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  finePushedOccupationEnvelope S
    (booleanComplementEvent fineEvent)
    (booleanComplementEvent coarseEvent)

/-- The original mismatch is bounded by the fine and pushed occupations of
the complementary event pair. -/
theorem coherentEventRawMismatchAverage_le_complementFinePushed
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentEventRawMismatchAverage S fineEvent coarseEvent ≤
      complementFinePushedOccupationEnvelope
        S fineEvent coarseEvent := by
  refine Q'.le_trans' _
    (coherentEventRawMismatchAverage S
      (booleanComplementEvent fineEvent)
      (booleanComplementEvent coarseEvent)) _ ?_ ?_
  · exact Q'.ge_of_eqv
      (coherentEventRawMismatchAverage_complement
        S fineEvent coarseEvent)
  · exact Q'.le_trans' _
      (coherentEventOccupationEnvelope S
        (booleanComplementEvent fineEvent)
        (booleanComplementEvent coarseEvent)) _
      (coherentEventRawMismatchAverage_le_occupationEnvelope S _ _)
      (coherentEventOccupationEnvelope_le_finePushed S _ _)

/-! ## 3. Positive-time faces controlled by zero-event probabilities -/

def lowerPositiveTimeComplementOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  complementFinePushedOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineRoot)
    (slabPhysicalFacePositiveB G.coarseRoot)

def reflectedPositiveTimeComplementOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  complementFinePushedOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineReflected)
    (slabPhysicalFacePositiveB G.coarseReflected)

def lowerReflectedPositiveTimeComplementOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  complementFinePushedOccupationEnvelope S
    (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

theorem enrichedLowerPositiveTimeDefectAverage_le_complementOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerPositiveTimeDefectAverage S G ≤
      lowerPositiveTimeComplementOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentLowerPositiveTimeRawMismatchAverage S G) _
    (Q'.le_of_eqv
      (enrichedLowerPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentEventRawMismatchAverage_le_complementFinePushed S _ _)

theorem enrichedReflectedPositiveTimeDefectAverage_le_complementOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedReflectedPositiveTimeDefectAverage S G ≤
      reflectedPositiveTimeComplementOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentReflectedPositiveTimeRawMismatchAverage S G) _
    (Q'.le_of_eqv
      (enrichedReflectedPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentEventRawMismatchAverage_le_complementFinePushed S _ _)

theorem enrichedLowerReflectedPositiveTimeDefectAverage_le_complementOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G ≤
      lowerReflectedPositiveTimeComplementOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentLowerReflectedPositiveTimeRawMismatchAverage S G) _
    (Q'.le_of_eqv
      (enrichedLowerReflectedPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentEventRawMismatchAverage_le_complementFinePushed S _ _)

/-! ## Axiom audit -/

#print axioms cylinderPullbackMismatchEvent_complement
#print axioms coherentSelectedRawMismatchRatio_complement
#print axioms coherentEventRawMismatchAverage_complement
#print axioms coherentEventRawMismatchAverage_le_complementFinePushed
#print axioms enrichedLowerPositiveTimeDefectAverage_le_complementOccupation
#print axioms enrichedReflectedPositiveTimeDefectAverage_le_complementOccupation
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_le_complementOccupation

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeComplementEnvelope
