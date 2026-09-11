/-
# Raw-weight form of the coherent positive-time mismatch

The weighted positive-time defect is supported exactly on positive coherent
rows.  This module opens each surviving row.  For an arbitrary pair of fine
and coarse Boolean events it proves

  |E_recoupling[coarse event] - 1_(fine event)|

equal to the raw mass of precisely those coarse targets on which the two
event values disagree, divided by the complete positive recoupling row
partition.  The root, reflected, and joint face defects are instances of this
identity.  A dependent congruence theorem then rewrites all three global
defect averages as explicit normalized sums of selected whole-slab raw-weight
ratios.

The selected numerators contain the actual SU(2) packet-channel products and
globally shared link-multiplicity factors.  No estimate for their ratio is
claimed here; that is the next analytic frontier.  In particular this module
does not claim reflection positivity, a transfer gap, a cutoff-tower limit,
or a continuum theorem.

## Axiom gate

Finite Boolean event partitions, exact positive-rational division, and
dependent finite-sum congruence only.  No classical choice, placeholder,
trusted external computation, computability escape, heartbeat increase, or
new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
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

private theorem sub_one_eqv_neg_of_add_eqv_one
    (left right : Q') (htotal : left + right ≈ 1) :
    left - 1 ≈ -right := by
  refine Q'.eqv_trans _ (left + (-(left + right))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm htotal))
  refine Q'.eqv_trans _ (left + ((-left) + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_add_eqv left right)
  refine Q'.eqv_trans _ ((left + (-left)) + (-right)) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.add_assoc_eqv left (-left) (-right))
  refine Q'.eqv_trans _ (0 + (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-right)
      (Q'.add_neg_self_eqv left)
  · exact Q'.eqv_of_eq (Q'.zero_add' (-right))

/-! ## 1. Conditional event moments and their raw ratios -/

private theorem coherentRecouplingEventMoment_eqv_finiteEventMass
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseEvent : EdgeLabelling → Bool) :
    coherentRecouplingEventMoment S source hpartition coarseEvent ≈
      finiteEventMass
        (wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition))
        S.coarse.physicalLabellings coarseEvent := by
  unfold coherentRecouplingEventMoment finiteEventMass
  apply listQSum_congr_on
  intro coarseState _
  cases hevent : coarseEvent coarseState
  · simp only [rationalBoolIndicator,
      Bool.false_eq_true, if_false]
    exact Q'.mul_zero_eqv _
  · simp only [rationalBoolIndicator, if_true]
    exact Q'.mul_one_eqv _

private theorem finiteEventMass_add_complement_eqv_total
    {A : Type} (mass : A → Q') (states : List A)
    (event : A → Bool) :
    finiteEventMass mass states event +
        finiteEventMass mass states (fun state => !(event state)) ≈
      listQSum mass states := by
  unfold finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then mass state else 0) +
          (if !(event state) then mass state else 0))
      states) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_add
        (fun state => if event state then mass state else 0)
        (fun state => if !(event state) then mass state else 0)
        states)
  · apply listQSum_congr_on
    intro state _
    cases hevent : event state
    · simp only [Bool.not_false, Bool.false_eq_true,
        if_false, if_true]
      exact Q'.eqv_of_eq (Q'.zero_add' (mass state))
    · simp only [Bool.not_true, if_true]
      exact Q'.eqv_of_eq (Q'.add_zero' (mass state))

/-- Raw selected-mismatch numerator divided by the complete positive
whole-slab recoupling partition. -/
def coherentSelectedRawMismatchRatio
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  wholeSlabRecouplingRawCylinderRatio
    (coherentSlabRecouplingSourceOfRawPartitionPos
      S source.1 source.2 hpartition)
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source.1)

/-- Exact Boolean row identity: the coherent conditional expectation defect
is the selected raw mismatch ratio. -/
theorem coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    Q'.abs
        (coherentRecouplingEventMoment S source hpartition coarseEvent -
          rationalBoolIndicator (fineEvent source.1)) ≈
      coherentSelectedRawMismatchRatio
        S source hpartition fineEvent coarseEvent := by
  let coherent := coherentSlabRecouplingSourceOfRawPartitionPos
    S source.1 source.2 hpartition
  let eventMass := finiteEventMass
    (wholeSlabRecouplingConditionalKernel coherent)
    S.coarse.physicalLabellings coarseEvent
  have hmoment :
      coherentRecouplingEventMoment S source hpartition coarseEvent ≈
        eventMass :=
    coherentRecouplingEventMoment_eqv_finiteEventMass
      S source hpartition coarseEvent
  have heventNonnegative : (0 : Q') ≤ eventMass :=
    finiteEventMass_nonnegative
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings coarseEvent
      (fun target _ =>
        wholeSlabRecouplingConditionalKernel_nonnegative coherent target)
  cases hfine : fineEvent source.1
  · have hraw : eventMass ≈
        wholeSlabRecouplingRawCylinderRatio coherent coarseEvent :=
      conditionalKernelCylinderMass_eqv_rawCylinderRatio
        coherent coarseEvent
    unfold rationalBoolIndicator coherentSelectedRawMismatchRatio
      cylinderPullbackMismatchEvent
    rw [hfine]
    simp only [Bool.false_eq_true, if_false]
    refine Q'.eqv_trans _ (Q'.abs eventMass) _ ?_ ?_
    · apply Q'.abs_eqv_congr
      exact Q'.eqv_trans _ (eventMass - 0) _
        (Q'.add_eqv_congr' hmoment (Q'.eqv_refl _))
        (Q'.eqv_of_eq (Q'.sub_zero' eventMass))
    refine Q'.eqv_trans _ eventMass _ ?_ hraw
    exact Q'.eqv_of_eq (ExpNeg.abs_of_nonneg heventNonnegative)
  · let complementMass := finiteEventMass
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings
      (fun target => !(coarseEvent target))
    have htotal : eventMass + complementMass ≈ 1 :=
      Q'.eqv_trans _
        (listQSum
          (wholeSlabRecouplingConditionalKernel coherent)
          S.coarse.physicalLabellings) _
        (finiteEventMass_add_complement_eqv_total
          (wholeSlabRecouplingConditionalKernel coherent)
          S.coarse.physicalLabellings coarseEvent)
        (wholeSlabRecouplingConditionalKernel_row_normalized coherent)
    have hcomplementNonnegative : (0 : Q') ≤ complementMass :=
      finiteEventMass_nonnegative
        (wholeSlabRecouplingConditionalKernel coherent)
        S.coarse.physicalLabellings
        (fun target => !(coarseEvent target))
        (fun target _ =>
          wholeSlabRecouplingConditionalKernel_nonnegative coherent target)
    have hraw : complementMass ≈
        wholeSlabRecouplingRawCylinderRatio coherent
          (fun target => !(coarseEvent target)) :=
      conditionalKernelCylinderMass_eqv_rawCylinderRatio
        coherent (fun target => !(coarseEvent target))
    unfold rationalBoolIndicator coherentSelectedRawMismatchRatio
      cylinderPullbackMismatchEvent
    rw [hfine]
    simp only [if_true]
    refine Q'.eqv_trans _ (Q'.abs (-complementMass)) _ ?_ ?_
    · apply Q'.abs_eqv_congr
      exact Q'.eqv_trans _ (eventMass - 1) _
        (Q'.add_eqv_congr' hmoment (Q'.eqv_refl _))
        (sub_one_eqv_neg_of_add_eqv_one
          eventMass complementMass htotal)
    refine Q'.eqv_trans _ (Q'.abs complementMass) _
      (Q'.abs_neg' complementMass) ?_
    refine Q'.eqv_trans _ complementMass _ ?_ hraw
    exact Q'.eqv_of_eq
      (ExpNeg.abs_of_nonneg hcomplementNonnegative)

/-! ## 2. Root, reflected, and joint raw mismatch ratios -/

def coherentLowerPositiveTimeRawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentSelectedRawMismatchRatio S source hpartition
    (slabPhysicalFacePositiveB G.fineRoot)
    (slabPhysicalFacePositiveB G.coarseRoot)

def coherentReflectedPositiveTimeRawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentSelectedRawMismatchRatio S source hpartition
    (slabPhysicalFacePositiveB G.fineReflected)
    (slabPhysicalFacePositiveB G.coarseReflected)

def coherentLowerReflectedPositiveTimeRawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentSelectedRawMismatchRatio S source hpartition
    (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
    (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

private theorem positiveTimeProduct_eqv_finePairIndicator
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (physical : EdgeLabelling) :
    (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralLowerRestriction S.fine.half physical) *
        (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
          (centralReflectedUpperRestriction S.fine.half physical) ≈
      rationalBoolIndicator
        (slabPhysicalFacePairPositiveB
          G.fineRoot G.fineReflected physical) := by
  refine Q'.eqv_trans _
    (rationalBoolIndicator
        (slabPhysicalFacePositiveB G.fineRoot physical) *
      rationalBoolIndicator
        (slabPhysicalFacePositiveB G.fineReflected physical)) _ ?_ ?_
  · exact mul_eqv_both_local
      (Q'.eqv_of_eq
        (slabPhysicalFacePositiveUnitObservable_lowerRestriction
          G.fineRoot_lower physical))
      (Q'.eqv_of_eq
        (slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
          G.fineRoot_lower physical))
  · exact Q'.eqv_symm (rationalBoolIndicator_and_local _ _)

theorem coherentLowerPositiveTimeDefect_eqv_rawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    coherentLowerPositiveTimeDefect G source hpartition ≈
      coherentLowerPositiveTimeRawMismatchRatio G source hpartition := by
  refine Q'.eqv_trans _
    (Q'.abs
      (coherentRecouplingEventMoment S source hpartition
          (slabPhysicalFacePositiveB G.coarseRoot) -
        rationalBoolIndicator
          (slabPhysicalFacePositiveB G.fineRoot source.1))) _ ?_ ?_
  · unfold coherentLowerPositiveTimeDefect coherentLowerFaceMoment
    apply Q'.abs_eqv_congr
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_of_eq
          (slabPhysicalFacePositiveUnitObservable_lowerRestriction
            G.fineRoot_lower source.1)))
  · exact coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
      S source hpartition
      (slabPhysicalFacePositiveB G.fineRoot)
      (slabPhysicalFacePositiveB G.coarseRoot)

theorem coherentReflectedPositiveTimeDefect_eqv_rawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    coherentReflectedPositiveTimeDefect G source hpartition ≈
      coherentReflectedPositiveTimeRawMismatchRatio
        G source hpartition := by
  refine Q'.eqv_trans _
    (Q'.abs
      (coherentRecouplingEventMoment S source hpartition
          (slabPhysicalFacePositiveB G.coarseReflected) -
        rationalBoolIndicator
          (slabPhysicalFacePositiveB G.fineReflected source.1))) _ ?_ ?_
  · unfold coherentReflectedPositiveTimeDefect
      coherentReflectedFaceMoment
    apply Q'.abs_eqv_congr
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_of_eq
          (slabPhysicalFacePositiveUnitObservable_reflectedUpperRestriction
            G.fineRoot_lower source.1)))
  · exact coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
      S source hpartition
      (slabPhysicalFacePositiveB G.fineReflected)
      (slabPhysicalFacePositiveB G.coarseReflected)

theorem coherentLowerReflectedPositiveTimeDefect_eqv_rawMismatchRatio
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    coherentLowerReflectedPositiveTimeDefect G source hpartition ≈
      coherentLowerReflectedPositiveTimeRawMismatchRatio
        G source hpartition := by
  refine Q'.eqv_trans _
    (Q'.abs
      (coherentRecouplingEventMoment S source hpartition
          (slabPhysicalFacePairPositiveB
            G.coarseRoot G.coarseReflected) -
        rationalBoolIndicator
          (slabPhysicalFacePairPositiveB
            G.fineRoot G.fineReflected source.1))) _ ?_ ?_
  · unfold coherentLowerReflectedPositiveTimeDefect
      coherentLowerReflectedFaceMoment
    apply Q'.abs_eqv_congr
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (positiveTimeProduct_eqv_finePairIndicator G source.1))
  · exact coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
      S source hpartition
      (slabPhysicalFacePairPositiveB G.fineRoot G.fineReflected)
      (slabPhysicalFacePairPositiveB G.coarseRoot G.coarseReflected)

/-! ## 3. Exact global raw-ratio averages -/

private theorem positiveCoherentWeightedDefectAux_congr
    (S : SlabScalePair)
    (left right :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hrow : ∀ source hpartition,
      left source hpartition ≈ right source hpartition) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      positiveCoherentWeightedDefectAux S left sources ≈
        positiveCoherentWeightedDefectAux S right sources
  | [] => Q'.eqv_refl 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left
              (S.fine.normalizedMass source.1) _ _
              (hrow source hpartition))
            (positiveCoherentWeightedDefectAux_congr
              S left right hrow tail)
        · simp only [positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_neg hpartition]
          exact positiveCoherentWeightedDefectAux_congr
            S left right hrow tail
      · simp only [positiveCoherentWeightedDefectAux,
          dif_neg hpositive]
        exact positiveCoherentWeightedDefectAux_congr
          S left right hrow tail

theorem positiveCoherentWeightedDefect_congr
    (S : SlabScalePair)
    (left right :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hrow : ∀ source hpartition,
      left source hpartition ≈ right source hpartition) :
    positiveCoherentWeightedDefect S left ≈
      positiveCoherentWeightedDefect S right := by
  unfold positiveCoherentWeightedDefect
  exact positiveCoherentWeightedDefectAux_congr
    S left right hrow (slabPhysicalSourceEntries S.fine)

def coherentLowerPositiveTimeRawMismatchAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentLowerPositiveTimeRawMismatchRatio G)

def coherentReflectedPositiveTimeRawMismatchAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentReflectedPositiveTimeRawMismatchRatio G)

def coherentLowerReflectedPositiveTimeRawMismatchAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentLowerReflectedPositiveTimeRawMismatchRatio G)

theorem enrichedLowerPositiveTimeDefectAverage_eqv_rawMismatch
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerPositiveTimeDefectAverage S G ≈
      coherentLowerPositiveTimeRawMismatchAverage S G := by
  exact Q'.eqv_trans _
    (coherentLowerPositiveTimeDefectAverage S G) _
    (enrichedLowerPositiveTimeDefectAverage_eqv_coherent S G)
    (positiveCoherentWeightedDefect_congr S _ _
      (fun source hpartition =>
        coherentLowerPositiveTimeDefect_eqv_rawMismatchRatio
          G source hpartition))

theorem enrichedReflectedPositiveTimeDefectAverage_eqv_rawMismatch
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedReflectedPositiveTimeDefectAverage S G ≈
      coherentReflectedPositiveTimeRawMismatchAverage S G := by
  exact Q'.eqv_trans _
    (coherentReflectedPositiveTimeDefectAverage S G) _
    (enrichedReflectedPositiveTimeDefectAverage_eqv_coherent S G)
    (positiveCoherentWeightedDefect_congr S _ _
      (fun source hpartition =>
        coherentReflectedPositiveTimeDefect_eqv_rawMismatchRatio
          G source hpartition))

theorem enrichedLowerReflectedPositiveTimeDefectAverage_eqv_rawMismatch
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G ≈
      coherentLowerReflectedPositiveTimeRawMismatchAverage S G := by
  exact Q'.eqv_trans _
    (coherentLowerReflectedPositiveTimeDefectAverage S G) _
    (enrichedLowerReflectedPositiveTimeDefectAverage_eqv_coherent S G)
    (positiveCoherentWeightedDefect_congr S _ _
      (fun source hpartition =>
        coherentLowerReflectedPositiveTimeDefect_eqv_rawMismatchRatio
          G source hpartition))

/-! ## Axiom audit -/

#print axioms coherentRecouplingEventDefect_eqv_selectedRawMismatchRatio
#print axioms coherentLowerPositiveTimeDefect_eqv_rawMismatchRatio
#print axioms coherentLowerReflectedPositiveTimeDefect_eqv_rawMismatchRatio
#print axioms positiveCoherentWeightedDefect_congr
#print axioms enrichedLowerPositiveTimeDefectAverage_eqv_rawMismatch
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_eqv_rawMismatch

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeRawMismatch
