/-
# Physical pushed-law form of the positive-time occupation envelope

The coherent mismatch envelope has two terms.  This module identifies both
with canonical finite-law quantities:

* coherent fine-source occupation is bounded by the corresponding event mass
  under the complete normalized fine Gibbs law;
* coherent coarse-output occupation is exactly the event mass of the
  coarse-only observable under the lossless enriched pushed law.

The second identity is a finite Fubini theorem plus an exact source-regime
decomposition.  Positive coherent rows supply the coarse event moment,
positive incoherent rows land in the retained sector where the coarse-only
observable is zero, and Gibbs-null rows have zero normalized source mass.

The resulting physical occupation envelope still has no claimed smallness.
In particular no uniform coupling, cutoff, volume, or lattice-spacing bound,
reflection positivity, transfer gap, cutoff-tower limit, or continuum theorem
is asserted here.

## Axiom gate

Attached-list recursion, finite Fubini, and exact positive-rational algebra
only.  No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeOccupationEnvelope
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coherent fine occupation sits inside the full fine event -/

private theorem rationalBoolIndicator_nonnegative_local (value : Bool) :
    (0 : Q') ≤ rationalBoolIndicator value := by
  cases value <;> decide

private theorem positiveCoherentIndicatorAux_le_fullAux
    (S : SlabScalePair) (event : EdgeLabelling → Bool) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      positiveCoherentWeightedDefectAux S
          (fun source _ => rationalBoolIndicator (event source.1))
          sources ≤
        listQSum
          (fun source =>
            S.fine.normalizedMass source.1 *
              rationalBoolIndicator (event source.1))
          sources
  | [] => Q'.le_refl' 0
  | source :: tail => by
      let head := S.fine.normalizedMass source.1 *
        rationalBoolIndicator (event source.1)
      let fullTail := listQSum
        (fun item : SlabPhysicalSourceEntry S.fine =>
          S.fine.normalizedMass item.1 *
            rationalBoolIndicator (event item.1))
        tail
      have htail :
          positiveCoherentWeightedDefectAux S
              (fun item _ => rationalBoolIndicator (event item.1)) tail ≤
            fullTail :=
        positiveCoherentIndicatorAux_le_fullAux S event tail
      have hheadNonnegative : (0 : Q') ≤ head :=
        Q'.mul_nonneg _ _
          (S.fine.normalizedMass_nonnegative source.1)
          (rationalBoolIndicator_nonnegative_local (event source.1))
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [positiveCoherentWeightedDefectAux, listQSum,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.add_le_add (Q'.le_refl' head) htail
        · simp only [positiveCoherentWeightedDefectAux, listQSum,
            dif_pos hpositive, dif_neg hpartition]
          exact Q'.le_trans' _ fullTail _ htail
            (Q'.le_trans' _ (fullTail + head) _
              (Q'.add_le_self_of_nonneg fullTail head hheadNonnegative)
              (Q'.le_of_eqv (Q'.add_comm_eqv fullTail head)))
      · simp only [positiveCoherentWeightedDefectAux, listQSum,
          dif_neg hpositive]
        exact Q'.le_trans' _ fullTail _ htail
          (Q'.le_trans' _ (fullTail + head) _
            (Q'.add_le_self_of_nonneg fullTail head hheadNonnegative)
            (Q'.le_of_eqv (Q'.add_comm_eqv fullTail head)))

private theorem fineIndicatorExpectation_eqv_normalizedEventMass
    (S : SlabScalePair) (event : EdgeLabelling → Bool) :
    allCutoffFinePhysicalExpectation S
        (fun source => rationalBoolIndicator (event source.1)) ≈
      normalizedSlabEventMass S.fine event := by
  unfold allCutoffFinePhysicalExpectation normalizedSlabEventMass
    finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        S.fine.normalizedMass physical *
          rationalBoolIndicator (event physical))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (fun physical =>
          S.fine.normalizedMass physical *
            rationalBoolIndicator (event physical))
        S.fine.physicalLabellings)
  · apply listQSum_congr_on
    intro physical _
    cases hevent : event physical
    · simp only [rationalBoolIndicator, Bool.false_eq_true, if_false]
      exact Q'.mul_zero_eqv _
    · simp only [rationalBoolIndicator, if_true]
      exact Q'.mul_one_eqv _

/-- The coherent-source occupation is an actual submass of the complete
normalized fine event probability. -/
theorem coherentFineEventSourceMass_le_normalizedSlabEventMass
    (S : SlabScalePair) (event : EdgeLabelling → Bool) :
    coherentFineEventSourceMass S event ≤
      normalizedSlabEventMass S.fine event := by
  refine Q'.le_trans' _
    (allCutoffFinePhysicalExpectation S
      (fun source => rationalBoolIndicator (event source.1))) _ ?_ ?_
  · unfold coherentFineEventSourceMass positiveCoherentWeightedDefect
      allCutoffFinePhysicalExpectation
    exact positiveCoherentIndicatorAux_le_fullAux S event
      (slabPhysicalSourceEntries S.fine)
  · exact Q'.le_of_eqv
      (fineIndicatorExpectation_eqv_normalizedEventMass S event)

/-! ## 2. Coherent coarse occupation is a pushed-law event mass -/

/-- Enriched target observable which sees a coarse Boolean event and is
identically zero on the retained fine-intertwiner sector. -/
def coarseOnlyEventB
    (coarseEvent : EdgeLabelling → Bool)
    (target : AllCutoffRetainedTarget) : Bool :=
  match target with
  | .inl coarseState => coarseEvent coarseState
  | .inr _ => false

def coarseOnlyEventIndicator
    (coarseEvent : EdgeLabelling → Bool)
    (target : AllCutoffRetainedTarget) : Q' :=
  allCutoffRetainedBranchEventIndicator
    (fun _ => false) coarseEvent target

private theorem coarseOnlyEventIndicator_eq_rationalBoolIndicator
    (coarseEvent : EdgeLabelling → Bool)
    (target : AllCutoffRetainedTarget) :
    coarseOnlyEventIndicator coarseEvent target =
      rationalBoolIndicator (coarseOnlyEventB coarseEvent target) := by
  cases target <;> rfl

/-- Canonical event mass of the coarse-only cylinder under the lossless
enriched pushed law. -/
def coherentPushedCoarseEventMass
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) : Q' :=
  allCutoffRetainedBlockedExpectation S
    (coarseOnlyEventIndicator coarseEvent)

/-- The pushed coarse occupation really is the finite mass of the named
Boolean event on the disjoint enriched carrier. -/
theorem coherentPushedCoarseEventMass_eqv_finiteEventMass
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) :
    coherentPushedCoarseEventMass S coarseEvent ≈
      finiteEventMass
        (allCutoffRetainedFineIntertwinerBlockedMass S)
        (allCutoffRetainedTargets S)
        (coarseOnlyEventB coarseEvent) := by
  unfold coherentPushedCoarseEventMass
    allCutoffRetainedBlockedExpectation finiteEventMass
  apply listQSum_congr_on
  intro target _
  rw [coarseOnlyEventIndicator_eq_rationalBoolIndicator]
  cases hevent : coarseOnlyEventB coarseEvent target
  · simp only [rationalBoolIndicator, Bool.false_eq_true, if_false]
    exact Q'.mul_zero_eqv _
  · simp only [rationalBoolIndicator, if_true]
    exact Q'.mul_one_eqv _

private theorem fineCoarseOnlyPullbackSum_eqv_coherentOutputAux
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      listQSum
          (fun source =>
            S.fine.normalizedMass source.1 *
              allCutoffRetainedObservablePullback S
                (coarseOnlyEventIndicator coarseEvent) source)
          sources ≈
        positiveCoherentWeightedDefectAux S
          (fun source hpartition =>
            coherentRecouplingEventMoment
              S source hpartition coarseEvent)
          sources
  | [] => Q'.eqv_refl 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [listQSum, positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left
              (S.fine.normalizedMass source.1) _ _
              (allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
                S source hpositive hpartition (fun _ => false) coarseEvent))
            (fineCoarseOnlyPullbackSum_eqv_coherentOutputAux
              S coarseEvent tail)
        · simp only [listQSum, positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_neg hpartition]
          have hpullbackZero :
              allCutoffRetainedObservablePullback S
                  (coarseOnlyEventIndicator coarseEvent) source ≈ 0 :=
            Q'.eqv_trans _
              (rationalBoolIndicator false) _
              (allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
                S source hpositive hpartition
                (fun _ => false) coarseEvent)
              (by decide)
          refine Q'.eqv_trans _
            (0 + positiveCoherentWeightedDefectAux S
              (fun item hitem =>
                coherentRecouplingEventMoment
                  S item hitem coarseEvent) tail) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.eqv_trans _
                (S.fine.normalizedMass source.1 * 0) _
                (Q'.mul_eqv_congr_left
                  (S.fine.normalizedMass source.1) _ _ hpullbackZero)
                (Q'.mul_zero_eqv _))
              (fineCoarseOnlyPullbackSum_eqv_coherentOutputAux
                S coarseEvent tail)
          · exact Q'.eqv_of_eq (Q'.zero_add' _)
      · simp only [listQSum, positiveCoherentWeightedDefectAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positiveCoherentWeightedDefectAux S
            (fun item hitem =>
              coherentRecouplingEventMoment
                S item hitem coarseEvent) tail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * allCutoffRetainedObservablePullback S
                (coarseOnlyEventIndicator coarseEvent) source) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source.1 hpositive))
              (Q'.zero_mul_eqv _))
            (fineCoarseOnlyPullbackSum_eqv_coherentOutputAux
              S coarseEvent tail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

private theorem fineCoarseOnlyPullbackExpectation_eqv_coherentOutputMass
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) :
    allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S
          (coarseOnlyEventIndicator coarseEvent)) ≈
      coherentCoarseEventOutputMass S coarseEvent := by
  unfold allCutoffFinePhysicalExpectation
    coherentCoarseEventOutputMass positiveCoherentWeightedDefect
  exact fineCoarseOnlyPullbackSum_eqv_coherentOutputAux
    S coarseEvent (slabPhysicalSourceEntries S.fine)

/-- The named coherent coarse-output occupation is exactly the coarse-only
event mass of the already constructed enriched pushed law. -/
theorem coherentCoarseEventOutputMass_eqv_pushedCoarseEventMass
    (S : SlabScalePair) (coarseEvent : EdgeLabelling → Bool) :
    coherentCoarseEventOutputMass S coarseEvent ≈
      coherentPushedCoarseEventMass S coarseEvent := by
  refine Q'.eqv_trans _
    (allCutoffFinePhysicalExpectation S
      (allCutoffRetainedObservablePullback S
        (coarseOnlyEventIndicator coarseEvent))) _ ?_ ?_
  · exact Q'.eqv_symm
      (fineCoarseOnlyPullbackExpectation_eqv_coherentOutputMass
        S coarseEvent)
  · exact Q'.eqv_symm
      (allCutoffRetainedBlockedExpectation_eqv_pullback
        S (coarseOnlyEventIndicator coarseEvent))

/-! ## 3. The fully canonical two-law occupation envelope -/

def finePushedOccupationEnvelope
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  normalizedSlabEventMass S.fine fineEvent +
    coherentPushedCoarseEventMass S coarseEvent

theorem coherentEventOccupationEnvelope_le_finePushed
    (S : SlabScalePair)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    coherentEventOccupationEnvelope S fineEvent coarseEvent ≤
      finePushedOccupationEnvelope S fineEvent coarseEvent := by
  unfold coherentEventOccupationEnvelope finePushedOccupationEnvelope
  exact Q'.add_le_add
    (coherentFineEventSourceMass_le_normalizedSlabEventMass S fineEvent)
    (Q'.le_of_eqv
      (coherentCoarseEventOutputMass_eqv_pushedCoarseEventMass
        S coarseEvent))

def lowerPositiveTimeFinePushedOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  finePushedOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineRoot)
    (slabPhysicalFacePositiveB G.coarseRoot)

def reflectedPositiveTimeFinePushedOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  finePushedOccupationEnvelope S
    (slabPhysicalFacePositiveB G.fineReflected)
    (slabPhysicalFacePositiveB G.coarseReflected)

def lowerReflectedPositiveTimeFinePushedOccupationEnvelope
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  finePushedOccupationEnvelope S
    (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

theorem enrichedLowerPositiveTimeDefectAverage_le_finePushedOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerPositiveTimeDefectAverage S G ≤
      lowerPositiveTimeFinePushedOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentLowerPositiveTimeOccupationEnvelope S G) _
    (enrichedLowerPositiveTimeDefectAverage_le_occupationEnvelope S G)
    (coherentEventOccupationEnvelope_le_finePushed S _ _)

theorem enrichedReflectedPositiveTimeDefectAverage_le_finePushedOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedReflectedPositiveTimeDefectAverage S G ≤
      reflectedPositiveTimeFinePushedOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentReflectedPositiveTimeOccupationEnvelope S G) _
    (enrichedReflectedPositiveTimeDefectAverage_le_occupationEnvelope S G)
    (coherentEventOccupationEnvelope_le_finePushed S _ _)

theorem enrichedLowerReflectedPositiveTimeDefectAverage_le_finePushedOccupation
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G ≤
      lowerReflectedPositiveTimeFinePushedOccupationEnvelope S G := by
  exact Q'.le_trans' _
    (coherentLowerReflectedPositiveTimeOccupationEnvelope S G) _
    (enrichedLowerReflectedPositiveTimeDefectAverage_le_occupationEnvelope S G)
    (coherentEventOccupationEnvelope_le_finePushed S _ _)

/-! ## Axiom audit -/

#print axioms coherentFineEventSourceMass_le_normalizedSlabEventMass
#print axioms coherentPushedCoarseEventMass_eqv_finiteEventMass
#print axioms coherentCoarseEventOutputMass_eqv_pushedCoarseEventMass
#print axioms coherentEventOccupationEnvelope_le_finePushed
#print axioms enrichedLowerPositiveTimeDefectAverage_le_finePushedOccupation
#print axioms enrichedReflectedPositiveTimeDefectAverage_le_finePushedOccupation
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_le_finePushedOccupation

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimePushedOccupation
