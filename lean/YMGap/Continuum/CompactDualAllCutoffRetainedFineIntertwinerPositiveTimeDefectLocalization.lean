/-
# Weighted localization of the enriched positive-time defect

The enriched block row has three source regimes.  Positive coherent rows are
sent through the genuine coarse recoupling law; positive incoherent rows are
retained without changing their physical state; Gibbs-null rows may use the
total-kernel completion but carry zero normalized source mass.

This module exploits that trichotomy at the exact weighted level.  A generic
finite recursion proves that any pullback defect which vanishes on positive
incoherent rows has its entire normalized-source average supported on the
positive coherent rows.  Applying it to the root, reflected, and joint face
moments shows that all retained and null contributions cancel exactly.  The
only remaining terms are the three coherent defects isolated by the previous
compiler.

This is support localization, not a smallness estimate.  No coherent defect
bound, reflection positivity, transfer gap, cutoff-tower convergence, or
continuum theorem is asserted here.

## Axiom gate

Dependent finite recursion, exact rational algebra, and zero mass of
nonpositive Gibbs rows only.  No classical choice, placeholder, trusted
external computation, computability escape, heartbeat increase, or new
axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A generic coherent-support recursion -/

/-- Normalized-source average of the absolute discrepancy between two
rowwise rational quantities. -/
def allCutoffPositiveTimeDefectAverage
    (S : SlabScalePair)
    (pullback fineValue : SlabPhysicalSourceEntry S.fine → Q') : Q' :=
  listQSum
    (fun source =>
      S.fine.normalizedMass source.1 *
        Q'.abs (pullback source - fineValue source))
    (slabPhysicalSourceEntries S.fine)

/-- Finite sum supported only on rows with both positive Gibbs weight and
positive whole-slab recoupling partition. -/
def positiveCoherentWeightedDefectAux
    (S : SlabScalePair)
    (rowDefect :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q') :
    List (SlabPhysicalSourceEntry S.fine) → Q'
  | [] => 0
  | source :: tail =>
      if _hpositive : (0 : Q') < S.fine.physicalTerm source.1 then
        if hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1 then
          S.fine.normalizedMass source.1 *
              rowDefect source hpartition +
            positiveCoherentWeightedDefectAux S rowDefect tail
        else
          positiveCoherentWeightedDefectAux S rowDefect tail
      else
        positiveCoherentWeightedDefectAux S rowDefect tail

def positiveCoherentWeightedDefect
    (S : SlabScalePair)
    (rowDefect :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q') : Q' :=
  positiveCoherentWeightedDefectAux S rowDefect
    (slabPhysicalSourceEntries S.fine)

private theorem pullback_sub_eqv_zero_of_eqv
    {pullback fineValue : Q'} (h : pullback ≈ fineValue) :
    pullback - fineValue ≈ 0 := by
  exact Q'.eqv_trans _ (fineValue + (-fineValue)) _
    (Q'.add_eqv_congr' h (Q'.eqv_refl _))
    (Q'.add_neg_self_eqv fineValue)

private theorem abs_eqv_zero_of_eqv_zero
    {value : Q'} (h : value ≈ 0) : Q'.abs value ≈ 0 := by
  exact Q'.eqv_trans _ (Q'.abs (0 : Q')) _
    (Q'.abs_eqv_congr h)
    (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (Q'.le_refl' 0)))

private theorem weightedDefectSum_eq_positiveCoherentAux
    (S : SlabScalePair)
    (pullback fineValue : SlabPhysicalSourceEntry S.fine → Q')
    (rowDefect :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hcoherent : ∀ source
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1),
      Q'.abs (pullback source - fineValue source) ≈
        rowDefect source hpartition)
    (hincoherent : ∀ source
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (_hnotPartition :
        ¬ (0 : Q') < wholeSlabRawRowPartition S source.1),
      pullback source ≈ fineValue source) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      listQSum
          (fun source =>
            S.fine.normalizedMass source.1 *
              Q'.abs (pullback source - fineValue source))
          sources ≈
        positiveCoherentWeightedDefectAux S rowDefect sources
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
              (hcoherent source hpositive hpartition))
            (weightedDefectSum_eq_positiveCoherentAux
              S pullback fineValue rowDefect hcoherent hincoherent tail)
        · simp only [listQSum, positiveCoherentWeightedDefectAux,
            dif_pos hpositive, dif_neg hpartition]
          have hrowZero :
              Q'.abs (pullback source - fineValue source) ≈ 0 :=
            abs_eqv_zero_of_eqv_zero
              (pullback_sub_eqv_zero_of_eqv
                (hincoherent source hpositive hpartition))
          refine Q'.eqv_trans _
            (0 + positiveCoherentWeightedDefectAux
              S rowDefect tail) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.eqv_trans _
                (S.fine.normalizedMass source.1 * 0) _
                (Q'.mul_eqv_congr_left
                  (S.fine.normalizedMass source.1) _ _ hrowZero)
                (Q'.mul_zero_eqv _))
              (weightedDefectSum_eq_positiveCoherentAux
                S pullback fineValue rowDefect
                hcoherent hincoherent tail)
          · exact Q'.eqv_of_eq (Q'.zero_add' _)
      · simp only [listQSum, positiveCoherentWeightedDefectAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positiveCoherentWeightedDefectAux
            S rowDefect tail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * Q'.abs (pullback source - fineValue source)) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source.1 hpositive))
              (Q'.zero_mul_eqv _))
            (weightedDefectSum_eq_positiveCoherentAux
              S pullback fineValue rowDefect
              hcoherent hincoherent tail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- Generic localization theorem: if the row discrepancy vanishes on every
positive incoherent row, its normalized average is exactly the positive
coherent-row sum. -/
theorem allCutoffPositiveTimeDefectAverage_eqv_positiveCoherent
    (S : SlabScalePair)
    (pullback fineValue : SlabPhysicalSourceEntry S.fine → Q')
    (rowDefect :
      (source : SlabPhysicalSourceEntry S.fine) →
        (0 : Q') < wholeSlabRawRowPartition S source.1 → Q')
    (hcoherent : ∀ source
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1),
      Q'.abs (pullback source - fineValue source) ≈
        rowDefect source hpartition)
    (hincoherent : ∀ source
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (_hnotPartition :
        ¬ (0 : Q') < wholeSlabRawRowPartition S source.1),
      pullback source ≈ fineValue source) :
    allCutoffPositiveTimeDefectAverage S pullback fineValue ≈
      positiveCoherentWeightedDefect S rowDefect := by
  unfold allCutoffPositiveTimeDefectAverage
    positiveCoherentWeightedDefect
  exact weightedDefectSum_eq_positiveCoherentAux
    S pullback fineValue rowDefect hcoherent hincoherent
    (slabPhysicalSourceEntries S.fine)

/-! ## 2. Root, reflected, and joint positive-time source values -/

def fineLowerPositiveTimeValue
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
    (centralLowerRestriction S.fine.half source.1)

def fineReflectedPositiveTimeValue
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
    (centralReflectedUpperRestriction S.fine.half source.1)

def fineLowerReflectedPositiveTimeValue
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  fineLowerPositiveTimeValue G source *
    fineReflectedPositiveTimeValue G source

def enrichedLowerPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffPositiveTimeDefectAverage S
    (allCutoffRetainedObservablePullback S
      (enrichedLowerFaceObservable G))
    (fineLowerPositiveTimeValue G)

def enrichedReflectedPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffPositiveTimeDefectAverage S
    (allCutoffRetainedObservablePullback S
      (enrichedReflectedFaceObservable G))
    (fineReflectedPositiveTimeValue G)

def enrichedLowerReflectedPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffPositiveTimeDefectAverage S
    (allCutoffRetainedObservablePullback S
      (enrichedLowerReflectedFaceObservable G))
    (fineLowerReflectedPositiveTimeValue G)

def coherentLowerPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentLowerPositiveTimeDefect G)

def coherentReflectedPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentReflectedPositiveTimeDefect G)

def coherentLowerReflectedPositiveTimeDefectAverage
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedDefect S
    (coherentLowerReflectedPositiveTimeDefect G)

/-! ## 3. Exact localization of the three physical defects -/

theorem enrichedLowerPositiveTimeDefectAverage_eqv_coherent
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerPositiveTimeDefectAverage S G ≈
      coherentLowerPositiveTimeDefectAverage S G := by
  unfold enrichedLowerPositiveTimeDefectAverage
    coherentLowerPositiveTimeDefectAverage
    fineLowerPositiveTimeValue
  apply allCutoffPositiveTimeDefectAverage_eqv_positiveCoherent
  · intro source hpositive hpartition
    exact coherentLowerPositiveTimeDefect_eqv_pullback
      G source hpositive hpartition
  · intro source hpositive hnotPartition
    exact enrichedLowerFacePullback_eqv_lowerPositiveTime_of_incoherent
      G source hpositive hnotPartition

theorem enrichedReflectedPositiveTimeDefectAverage_eqv_coherent
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedReflectedPositiveTimeDefectAverage S G ≈
      coherentReflectedPositiveTimeDefectAverage S G := by
  unfold enrichedReflectedPositiveTimeDefectAverage
    coherentReflectedPositiveTimeDefectAverage
    fineReflectedPositiveTimeValue
  apply allCutoffPositiveTimeDefectAverage_eqv_positiveCoherent
  · intro source hpositive hpartition
    exact coherentReflectedPositiveTimeDefect_eqv_pullback
      G source hpositive hpartition
  · intro source hpositive hnotPartition
    exact enrichedReflectedFacePullback_eqv_upperPositiveTime_of_incoherent
      G source hpositive hnotPartition

theorem enrichedLowerReflectedPositiveTimeDefectAverage_eqv_coherent
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedPositiveTimeDefectAverage S G ≈
      coherentLowerReflectedPositiveTimeDefectAverage S G := by
  unfold enrichedLowerReflectedPositiveTimeDefectAverage
    coherentLowerReflectedPositiveTimeDefectAverage
    fineLowerReflectedPositiveTimeValue
    fineLowerPositiveTimeValue fineReflectedPositiveTimeValue
  apply allCutoffPositiveTimeDefectAverage_eqv_positiveCoherent
  · intro source hpositive hpartition
    exact coherentLowerReflectedPositiveTimeDefect_eqv_pullback
      G source hpositive hpartition
  · intro source hpositive hnotPartition
    exact
      enrichedLowerReflectedFacePullback_eqv_positiveTimeProduct_of_incoherent
        G source hpositive hnotPartition

/-! ## Axiom audit -/

#print axioms positiveCoherentWeightedDefectAux
#print axioms allCutoffPositiveTimeDefectAverage_eqv_positiveCoherent
#print axioms enrichedLowerPositiveTimeDefectAverage_eqv_coherent
#print axioms enrichedReflectedPositiveTimeDefectAverage_eqv_coherent
#print axioms enrichedLowerReflectedPositiveTimeDefectAverage_eqv_coherent

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDefectLocalization
