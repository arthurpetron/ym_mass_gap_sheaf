/-
# Occupation envelope for the coherent positive-time mismatch

The exact raw-ratio formula does not make the mismatch small pointwise: an
occupied fine face may be removed with large conditional probability.  The
correct finite-volume estimate is weighted.  This module proves that the
normalized coherent mismatch average is bounded by the sum of

* the normalized source mass on which the fine event is occupied, and
* the normalized coherent output mass on which the coarse event is occupied.

The proof is the triangle inequality row by row, followed by an exact
dependent finite-sum compiler.  It is specialized to the lower, reflected,
and joint positive-time face events.

This is an occupation decomposition, not an occupation smallness theorem.
No coupling-, cutoff-, volume-, or lattice-spacing-uniform bound is claimed;
those remain analytic obligations.  In particular this module does not claim
reflection positivity, a transfer gap, a cutoff-tower limit, or a continuum
theorem.

## Axiom gate

Finite positive-rational sums, their monotonicity, and the rational triangle
inequality only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
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

private theorem rationalBoolIndicator_nonnegative_local (value : Bool) :
    (0 : Q') ≤ rationalBoolIndicator value := by
  cases value <;> decide

private theorem coherentRecouplingEventMoment_nonnegative
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseEvent : EdgeLabelling → Bool) :
    (0 : Q') ≤
      coherentRecouplingEventMoment S source hpartition coarseEvent := by
  unfold coherentRecouplingEventMoment
  apply listQSum_nonnegative_on
  intro coarseState _
  exact Q'.mul_nonneg _ _
    (wholeSlabRecouplingConditionalKernel_nonnegative
      (coherentSlabRecouplingSourceOfRawPartitionPos
        S source.1 source.2 hpartition) coarseState)
    (rationalBoolIndicator_nonnegative_local (coarseEvent coarseState))

/-! ## 1. The exact rowwise triangle envelope -/

/-- The selected raw mismatch ratio is at most the occupied fine indicator
plus the occupied coarse conditional moment.  This is intentionally not
presented as a small pointwise bound. -/
theorem coherentSelectedRawMismatchRatio_le_occupationEnvelope
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentSelectedRawMismatchRatio
        S source hpartition fineEvent coarseEvent ≤
      rationalBoolIndicator (fineEvent source.1) +
        coherentRecouplingEventMoment
          S source hpartition coarseEvent := by
  let moment := coherentRecouplingEventMoment
    S source hpartition coarseEvent
  let indicator := rationalBoolIndicator (fineEvent source.1)
  have hmomentNonnegative : (0 : Q') ≤ moment :=
    coherentRecouplingEventMoment_nonnegative
      S source hpartition coarseEvent
  have hindicatorNonnegative : (0 : Q') ≤ indicator :=
    rationalBoolIndicator_nonnegative_local (fineEvent source.1)
  have hraw :
      Q'.abs (moment - indicator) ≈
        coherentSelectedRawMismatchRatio
          S source hpartition fineEvent coarseEvent :=
    coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
      S source hpartition fineEvent coarseEvent
  refine Q'.le_trans' _ (Q'.abs (moment - indicator)) _
    (Q'.ge_of_eqv hraw) ?_
  refine Q'.le_trans' _
    (Q'.abs moment + Q'.abs (-indicator)) _
    (Q'.abs_add_le' moment (-indicator)) ?_
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _ (moment + indicator) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hmomentNonnegative))
      (Q'.eqv_trans _ (Q'.abs indicator) _
        (Q'.abs_neg' indicator)
        (Q'.eqv_of_eq
          (ExpNeg.abs_of_nonneg hindicatorNonnegative)))
  · exact Q'.add_comm_eqv moment indicator

/-! ## 2. Compile rowwise envelopes through the coherent source sum -/

private theorem add_interchange_local (a b c d : Q') :
    (a + b) + (c + d) ≈ (a + c) + (b + d) := by
  refine Q'.eqv_trans _ (a + (b + (c + d))) _
    (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ (a + ((b + c) + d)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a + ((c + b) + d)) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_eqv_congr_right _ _ d (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a + (c + (b + d))) _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a c (b + d))

private theorem positiveCoherentWeightedDefectAux_le_add
    (S : SlabScalePair)
    (value left right :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hrow : ∀ source hpartition,
      value source hpartition ≤
        left source hpartition + right source hpartition) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      positiveCoherentWeightedDefectAux S value sources ≤
        positiveCoherentWeightedDefectAux S left sources +
          positiveCoherentWeightedDefectAux S right sources
  | [] => Q'.le_refl' 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_pos hpartition]
          let mass := S.fine.normalizedMass source.1
          let valueHead := value source hpartition
          let leftHead := left source hpartition
          let rightHead := right source hpartition
          let valueTail := positiveCoherentWeightedDefectAux S value tail
          let leftTail := positiveCoherentWeightedDefectAux S left tail
          let rightTail := positiveCoherentWeightedDefectAux S right tail
          have hhead : mass * valueHead ≤
              mass * (leftHead + rightHead) :=
            Q'.mul_le_mul_of_nonneg_left _ _ mass
              (hrow source hpartition)
              (S.fine.normalizedMass_nonnegative source.1)
          have htail : valueTail ≤ leftTail + rightTail :=
            positiveCoherentWeightedDefectAux_le_add
              S value left right hrow tail
          refine Q'.le_trans' _
            (mass * (leftHead + rightHead) +
              (leftTail + rightTail)) _
            (Q'.add_le_add hhead htail) ?_
          apply Q'.le_of_eqv
          refine Q'.eqv_trans _
            ((mass * leftHead + mass * rightHead) +
              (leftTail + rightTail)) _ ?_ ?_
          · exact Q'.add_eqv_congr_right _ _ _
              (Q'.mul_add_eqv mass leftHead rightHead)
          · exact add_interchange_local
              (mass * leftHead) (mass * rightHead)
              leftTail rightTail
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_neg hpartition]
          exact positiveCoherentWeightedDefectAux_le_add
            S value left right hrow tail
      · simp only [positiveCoherentWeightedDefectAux,
          dif_neg hpositive]
        exact positiveCoherentWeightedDefectAux_le_add
          S value left right hrow tail

/-- A rowwise additive upper bound passes through the dependent normalized
positive-coherent source sum without losing a constant. -/
theorem positiveCoherentWeightedDefect_le_add
    (S : SlabScalePair)
    (value left right :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hrow : ∀ source hpartition,
      value source hpartition ≤
        left source hpartition + right source hpartition) :
    positiveCoherentWeightedDefect S value ≤
      positiveCoherentWeightedDefect S left +
        positiveCoherentWeightedDefect S right := by
  unfold positiveCoherentWeightedDefect
  exact positiveCoherentWeightedDefectAux_le_add
    S value left right hrow (slabPhysicalSourceEntries S.fine)

/-! ## 3. Named occupation terms and the averaged envelope -/

/-- Normalized mass of positive coherent sources on which the fine event is
occupied. -/
def coherentFineEventSourceMass
    (S : SlabScalePair) (fineEvent : EdgeLabelling → Bool) : Q' :=
  positiveCoherentWeightedDefect S
    (fun source _ => rationalBoolIndicator (fineEvent source.1))

/-- Normalized positive-coherent source average of the occupied coarse-event
conditional moment. -/
def coherentCoarseEventOutputMass
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) : Q' :=
  positiveCoherentWeightedDefect S
    (fun source hpartition =>
      coherentRecouplingEventMoment
        S source hpartition coarseEvent)

/-- The honest two-term occupation envelope for one fine/coarse event pair. -/
def coherentEventOccupationEnvelope
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  coherentFineEventSourceMass S fineEvent +
    coherentCoarseEventOutputMass S coarseEvent

/-- The normalized coherent average of exact selected raw mismatch ratios. -/
def coherentEventRawMismatchAverage
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  positiveCoherentWeightedDefect S
    (fun source hpartition =>
      coherentSelectedRawMismatchRatio
        S source hpartition fineEvent coarseEvent)

/-- The averaged raw mismatch is bounded, with unit coefficients, by fine
source occupation plus coherent coarse output occupation. -/
theorem coherentEventRawMismatchAverage_le_occupationEnvelope
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentEventRawMismatchAverage S fineEvent coarseEvent ≤
      coherentEventOccupationEnvelope S fineEvent coarseEvent := by
  unfold coherentEventRawMismatchAverage coherentEventOccupationEnvelope
    coherentFineEventSourceMass coherentCoarseEventOutputMass
  apply positiveCoherentWeightedDefect_le_add
  intro source hpartition
  exact coherentSelectedRawMismatchRatio_le_occupationEnvelope
    S source hpartition fineEvent coarseEvent

/-! ## 4. Lower, reflected, and joint face instances -/

def coherentLowerPositiveTimeOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  coherentEventOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineRoot)
    (slabPhysicalFacePositiveB G.coarseRoot)

def coherentReflectedPositiveTimeOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  coherentEventOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineReflected)
    (slabPhysicalFacePositiveB G.coarseReflected)

def coherentLowerReflectedPositiveTimeOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  coherentEventOccupationEnvelope S
    (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

theorem coherentLowerPositiveTimeRawMismatchAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    coherentLowerPositiveTimeRawMismatchAverage S G ≤
      coherentLowerPositiveTimeOccupationEnvelope S G := by
  exact coherentEventRawMismatchAverage_le_occupationEnvelope S _ _

theorem coherentReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    coherentReflectedPositiveTimeRawMismatchAverage S G ≤
      coherentReflectedPositiveTimeOccupationEnvelope S G := by
  exact coherentEventRawMismatchAverage_le_occupationEnvelope S _ _

theorem coherentLowerReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    coherentLowerReflectedPositiveTimeRawMismatchAverage S G ≤
      coherentLowerReflectedPositiveTimeOccupationEnvelope S G := by
  exact coherentEventRawMismatchAverage_le_occupationEnvelope S _ _

/-! ## 5. Return the envelope to the actual enriched defects -/

theorem enrichedLowerPositiveTimeDefectAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerPositiveTimeDefectAverage S G ≤
      coherentLowerPositiveTimeOccupationEnvelope S G := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedLowerPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentLowerPositiveTimeRawMismatchAverage_le_occupationEnvelope S G)

theorem enrichedReflectedPositiveTimeDefectAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedReflectedPositiveTimeDefectAverage S G ≤
      coherentReflectedPositiveTimeOccupationEnvelope S G := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedReflectedPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope S G)

theorem enrichedLowerReflectedPositiveTimeDefectAverage_le_occupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G ≤
      coherentLowerReflectedPositiveTimeOccupationEnvelope S G := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (enrichedLowerReflectedPositiveTimeDefectAverage_eqv_rawMismatch S G))
    (coherentLowerReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope
      S G)

/-! ## Axiom audit -/

#print axioms coherentSelectedRawMismatchRatio_le_occupationEnvelope
#print axioms positiveCoherentWeightedDefect_le_add
#print axioms coherentEventRawMismatchAverage_le_occupationEnvelope
#print axioms coherentLowerPositiveTimeRawMismatchAverage_le_occupationEnvelope
#print axioms coherentReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope
#print axioms coherentLowerReflectedPositiveTimeRawMismatchAverage_le_occupationEnvelope
#print axioms enrichedLowerPositiveTimeDefectAverage_le_occupationEnvelope
#print axioms enrichedReflectedPositiveTimeDefectAverage_le_occupationEnvelope
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_le_occupationEnvelope

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
