/-
# Positive raw-row form of the connected Gibbs-refresh action

The selected connected row action is now expanded on every strictly positive
fine Gibbs source.  The production contribution is the globally link-glued
whole-slab raw observable numerator divided by the complete positive row
partition; the reference contribution is the normalized coarse Gibbs
expectation of the same connected observable.

Fine sources whose physical term is not strictly positive have normalized
mass zero.  A dependent recursion therefore removes them exactly from both
the signed source average and the source-weighted selected-row `L1`.  This
leaves a literal positive-source raw-ratio target for the next recoupling or
posterior estimate, without paying full kernel-row variation.

No smallness estimate is asserted.  Cutoff/volume uniformity, continuum
persistence, OS/GNS reconstruction, the Hamiltonian gap, and the Yang--Mills
mass gap remain open.

Constructive contract: finite rational sums, positive rational division, and
the existing proof-carrying coherent sources only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRefreshSpectralComparison
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _) (listQSum_neg_local right items)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_swap_last_local (first second third : Q') :
    (first * second) * third ≈ (first * third) * second := by
  refine Q'.eqv_trans _ (first * (second * third)) _
    (Q'.mul_assoc_eqv first second third) ?_
  refine Q'.eqv_trans _ (first * (third * second)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left first _ _
      (Q'.mul_comm_eqv second third)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv first third second)

/-! ## 1. A raw numerator for an arbitrary rational observable -/

/-- Globally link-glued raw numerator of one rational coarse observable on a
proof-carrying strictly positive fine source. -/
def wholeSlabRecouplingRawObservableNumerator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun target =>
      wholeSlabRecouplingRawWeight S source.fineState target *
        observable target)
    S.coarse.physicalLabellings

/-- Raw observable numerator divided by the complete positive row
partition. -/
def wholeSlabRecouplingRawObservableRatio
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (observable : EdgeLabelling → Q') : Q' :=
  Q'.divPos
    (wholeSlabRecouplingRawObservableNumerator source observable)
    (wholeSlabRecouplingPartition source)
    (wholeSlabRecouplingPartition_pos source)

/-- The conditional recoupling-row expectation of any rational observable is
exactly its globally link-glued raw numerator divided by the full row
partition. -/
theorem conditionalKernelObservableExpectation_eqv_rawRatio
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (observable : EdgeLabelling → Q') :
    observableExpectation
        (wholeSlabRecouplingConditionalKernel source)
        S.coarse.physicalLabellings observable ≈
      wholeSlabRecouplingRawObservableRatio source observable := by
  unfold observableExpectation wholeSlabRecouplingConditionalKernel
    wholeSlabRecouplingRawObservableRatio
    wholeSlabRecouplingRawObservableNumerator Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (wholeSlabRecouplingRawWeight S source.fineState target *
          observable target) *
            Q'.recipPos (wholeSlabRecouplingPartition source)
              (wholeSlabRecouplingPartition_pos source))
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact mul_swap_last_local
      (wholeSlabRecouplingRawWeight S source.fineState target)
      (Q'.recipPos (wholeSlabRecouplingPartition source)
        (wholeSlabRecouplingPartition_pos source))
      (observable target)
  exact listQSum_mul_right
    (fun target =>
      wholeSlabRecouplingRawWeight S source.fineState target *
        observable target)
    (Q'.recipPos (wholeSlabRecouplingPartition source)
      (wholeSlabRecouplingPartition_pos source))
    S.coarse.physicalLabellings

private theorem finiteKernelDifferenceAction_eqv_expectation_sub
    {Source Target : Type} (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q') (source : Source) :
    finiteKernelDifferenceAction
        targets kernel reference observable source ≈
      listQSum
          (fun target => kernel source target * observable target)
          targets -
        listQSum
          (fun target => reference source target * observable target)
          targets := by
  unfold finiteKernelDifferenceAction
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        kernel source target * observable target -
          reference source target * observable target)
      targets) _ ?_ ?_
  · apply listQSum_congr
    intro target
    refine Q'.eqv_trans _
      (kernel source target * observable target +
        (-reference source target) * observable target) _ ?_ ?_
    · exact Q'.add_mul_eqv
        (kernel source target) (-reference source target)
        (observable target)
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_mul_eqv (reference source target) (observable target))
  exact listQSum_sub_local _ _ targets

/-! ## 2. The connected action on one positive physical source -/

/-- Literal positive-source raw-ratio difference for the connected
observable: production raw expectation minus normalized coarse Gibbs
expectation. -/
def positivePhysicalConnectedRawRowAction
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) : Q' :=
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let coherent := positiveCoherentSource S hfineCutoff hcoarseCoupling
    source hsource hpositive
  let observable := connectedRemainderObservable K M
  wholeSlabRecouplingRawObservableRatio coherent observable -
    observableExpectation S.coarse.normalizedMass
      S.coarse.physicalLabellings observable

/-- On every strictly positive fine Gibbs source, the selected production
minus refresh row action is exactly the explicit raw-ratio difference. -/
theorem coarseGibbsRefreshConnectedRowAction_eqv_positiveRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshConnectedRowAction
        S hfineCutoff hcoarseCoupling M source ≈
      positivePhysicalConnectedRawRowAction
        S hfineCutoff hcoarseCoupling source hsource hpositive M := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let coherent := positiveCoherentSource S hfineCutoff hcoarseCoupling
    source hsource hpositive
  let observable := connectedRemainderObservable K M
  let candidateExpectation :=
    observableExpectation (K.kernel source)
      S.coarse.physicalLabellings observable
  let refreshExpectation :=
    observableExpectation (coarseGibbsRefreshKernel S source)
      S.coarse.physicalLabellings observable
  let conditionalExpectation :=
    observableExpectation
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings observable
  let coarseExpectation :=
    observableExpectation S.coarse.normalizedMass
      S.coarse.physicalLabellings observable
  refine Q'.eqv_trans _
    (candidateExpectation - refreshExpectation) _ ?_ ?_
  · unfold coarseGibbsRefreshConnectedRowAction candidateExpectation
      refreshExpectation
    exact finiteKernelDifferenceAction_eqv_expectation_sub
      S.coarse.physicalLabellings K.kernel
      (coarseGibbsRefreshKernel S) observable source
  refine Q'.eqv_trans _
    (conditionalExpectation - coarseExpectation) _ ?_ ?_
  · exact sub_eqv_both_local
      (by
        unfold candidateExpectation conditionalExpectation
          observableExpectation K coherent physicalKernel
        apply listQSum_congr
        intro target
        exact Q'.mul_eqv_congr_right _ _ (observable target)
          (cutoffOneWholeSlabKernel_eq_positive
            S hfineCutoff hcoarseCoupling hsource hpositive target))
      (by
        unfold refreshExpectation coarseExpectation observableExpectation
        apply listQSum_congr
        intro target
        exact Q'.mul_eqv_congr_right _ _ (observable target)
          (coarseGibbsRefreshKernel_eqv_coarseNormalizedMass
            S source target))
  unfold positivePhysicalConnectedRawRowAction
  exact sub_eqv_both_local
    (by
      unfold conditionalExpectation
      exact conditionalKernelObservableExpectation_eqv_rawRatio
        coherent observable)
    (Q'.eqv_refl _)

/-! ## 3. Delete Gibbs-null rows from the signed average -/

/-- Positive-source recursion for the signed raw connected row average. -/
def positivePhysicalConnectedRawSignedSourceAverageAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        S.fine.normalizedMass source *
            positivePhysicalConnectedRawRowAction
              S hfineCutoff hcoarseCoupling source
              (hphysical source List.mem_cons_self) hpositive M +
          positivePhysicalConnectedRawSignedSourceAverageAux
            S hfineCutoff hcoarseCoupling M tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positivePhysicalConnectedRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- Complete signed average over exactly the strictly positive physical
fine sources. -/
def positivePhysicalConnectedRawSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  positivePhysicalConnectedRawSignedSourceAverageAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

private theorem connectedSignedSourceAverageSum_eq_rawAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              coarseGibbsRefreshConnectedRowAction
                S hfineCutoff hcoarseCoupling M source)
          sources ≈
        positivePhysicalConnectedRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum,
          positivePhysicalConnectedRawSignedSourceAverageAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (coarseGibbsRefreshConnectedRowAction_eqv_positiveRaw
              S hfineCutoff hcoarseCoupling source hsource hpositive M))
          (connectedSignedSourceAverageSum_eq_rawAux
            S hfineCutoff hcoarseCoupling M tail htail)
      · simp only [listQSum,
          positivePhysicalConnectedRawSignedSourceAverageAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positivePhysicalConnectedRawSignedSourceAverageAux
            S hfineCutoff hcoarseCoupling M tail htail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * coarseGibbsRefreshConnectedRowAction
                S hfineCutoff hcoarseCoupling M source) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv _))
            (connectedSignedSourceAverageSum_eq_rawAux
              S hfineCutoff hcoarseCoupling M tail htail)
        exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- Removing Gibbs-null rows preserves the signed selected-row average
exactly. -/
theorem coarseGibbsRefreshConnectedSignedSourceAverage_eqv_positiveRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshConnectedSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      positivePhysicalConnectedRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M := by
  unfold coarseGibbsRefreshConnectedSignedSourceAverage
    positivePhysicalConnectedRawSignedSourceAverage
  exact connectedSignedSourceAverageSum_eq_rawAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

/-- The positive-source raw-ratio average is therefore exactly the existing
centered cylinder remainder. -/
theorem positivePhysicalConnectedRawSignedSourceAverage_eqv_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (coarseGibbsRefreshConnectedSignedSourceAverage_eqv_positiveRaw
        S hfineCutoff hcoarseCoupling M))
    (coarseGibbsRefreshConnectedSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-! ## 4. Positive-row absolute and pointwise interfaces -/

/-- Positive-source recursion for the fine-weighted absolute selected raw
row action. -/
def positivePhysicalConnectedRawSourceL1Aux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        S.fine.normalizedMass source *
            Q'.abs
              (positivePhysicalConnectedRawRowAction
                S hfineCutoff hcoarseCoupling source
                (hphysical source List.mem_cons_self) hpositive M) +
          positivePhysicalConnectedRawSourceL1Aux
            S hfineCutoff hcoarseCoupling M tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positivePhysicalConnectedRawSourceL1Aux
          S hfineCutoff hcoarseCoupling M tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- Fine-weighted selected raw-row `L1` over exactly the positive sources. -/
def positivePhysicalConnectedRawSourceL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  positivePhysicalConnectedRawSourceL1Aux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

private theorem connectedSourceL1Sum_eq_rawAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              Q'.abs
                (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source))
          sources ≈
        positivePhysicalConnectedRawSourceL1Aux
          S hfineCutoff hcoarseCoupling M sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, positivePhysicalConnectedRawSourceL1Aux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (Q'.abs_eqv_congr
              (coarseGibbsRefreshConnectedRowAction_eqv_positiveRaw
                S hfineCutoff hcoarseCoupling source
                hsource hpositive M)))
          (connectedSourceL1Sum_eq_rawAux
            S hfineCutoff hcoarseCoupling M tail htail)
      · simp only [listQSum, positivePhysicalConnectedRawSourceL1Aux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positivePhysicalConnectedRawSourceL1Aux
            S hfineCutoff hcoarseCoupling M tail htail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * Q'.abs
                (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source)) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv _))
            (connectedSourceL1Sum_eq_rawAux
              S hfineCutoff hcoarseCoupling M tail htail)
        exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- Deleting Gibbs-null rows also preserves the fine-weighted selected-row
`L1` exactly. -/
theorem coarseGibbsRefreshConnectedSourceL1_eqv_positiveRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshConnectedSourceL1
        S hfineCutoff hcoarseCoupling M ≈
      positivePhysicalConnectedRawSourceL1
        S hfineCutoff hcoarseCoupling M := by
  unfold coarseGibbsRefreshConnectedSourceL1
    positivePhysicalConnectedRawSourceL1
  exact connectedSourceL1Sum_eq_rawAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

/-- Direct quadratic premise on the positive-source signed raw average. -/
def PositivePhysicalConnectedRawSignedSourceAverageCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (positivePhysicalConnectedRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M) ≤
    kernelCeiling * (g * g)

/-- Quadratic premise on the positive-source weighted absolute raw row
actions. -/
def PositivePhysicalConnectedRawSourceL1Calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  positivePhysicalConnectedRawSourceL1
      S hfineCutoff hcoarseCoupling M ≤
    kernelCeiling * (g * g)

/-- Pointwise quadratic premise only on strictly positive fine Gibbs rows. -/
def PositivePhysicalConnectedRawPointwiseCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  ∀ source (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source),
    Q'.abs
        (positivePhysicalConnectedRawRowAction
          S hfineCutoff hcoarseCoupling source hsource hpositive M) ≤
      kernelCeiling * (g * g)

/-- The direct raw signed-average premise is exactly equivalent to the
existing centered calibration. -/
theorem positiveRawSignedSourceAverageCalibration_iff_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold PositivePhysicalConnectedRawSignedSourceAverageCalibration
    CoarseGibbsRefreshConnectedRemainderCalibration
  have hexact :=
    positivePhysicalConnectedRawSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hexact))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hexact)) h

/-- The positive raw source-`L1` premise compiles with no coefficient loss. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawSourceL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hrawL1 : PositivePhysicalConnectedRawSourceL1Calibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  apply coarseGibbsRefreshConnectedRemainderCalibration_of_sourceL1
  unfold CoarseGibbsRefreshConnectedSourceL1Calibration
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (coarseGibbsRefreshConnectedSourceL1_eqv_positiveRaw
        S hfineCutoff hcoarseCoupling M))
    (by
      simpa only [PositivePhysicalConnectedRawSourceL1Calibration] using
        hrawL1)

/-- A pointwise estimate on only the strictly positive raw rows implies the
source-`L1` calibration; null rows cost nothing because their fine Gibbs mass
is exactly zero. -/
theorem coarseGibbsRefreshConnectedSourceL1Calibration_of_positiveRawPointwise
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hpointwise : PositivePhysicalConnectedRawPointwiseCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedSourceL1Calibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold CoarseGibbsRefreshConnectedSourceL1Calibration
    coarseGibbsRefreshConnectedSourceL1
  let budget := kernelCeiling * (g * g)
  have hsum :
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              Q'.abs
                (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source))
          S.fine.physicalLabellings ≤
        listQSum
          (fun source => S.fine.normalizedMass source * budget)
          S.fine.physicalLabellings := by
    apply listQSum_mono
    intro source hsource
    by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
    · apply Q'.mul_le_mul_of_nonneg_left
      · exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.abs_eqv_congr
              (coarseGibbsRefreshConnectedRowAction_eqv_positiveRaw
                S hfineCutoff hcoarseCoupling source
                hsource hpositive M)))
          (by
            unfold PositivePhysicalConnectedRawPointwiseCalibration at hpointwise
            simpa only [budget] using
              hpointwise source hsource hpositive)
      · exact S.fine.normalizedMass_nonnegative source
    · have hmass := normalizedMass_eqv_zero_of_not_positive
          S.fine source hpositive
      have hleft :
          S.fine.normalizedMass source *
              Q'.abs
                (coarseGibbsRefreshConnectedRowAction
                  S hfineCutoff hcoarseCoupling M source) ≈ 0 := by
        refine Q'.eqv_trans _
          (0 * Q'.abs
            (coarseGibbsRefreshConnectedRowAction
              S hfineCutoff hcoarseCoupling M source)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ hmass
        exact Q'.zero_mul_eqv _
      have hright : S.fine.normalizedMass source * budget ≈ 0 := by
        refine Q'.eqv_trans _ (0 * budget) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ hmass
        exact Q'.zero_mul_eqv _
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hleft) (Q'.ge_of_eqv hright)
  refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _
    (listQSum S.fine.normalizedMass S.fine.physicalLabellings * budget) _
    (listQSum_mul_right S.fine.normalizedMass budget
      S.fine.physicalLabellings) ?_
  refine Q'.eqv_trans _ ((1 : Q') * budget) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ budget S.fine.normalizedMass_total
  exact Q'.one_mul_eqv budget

/-- The strictly-positive raw-row pointwise estimate compiles directly to the
existing normalized connected remainder. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawPointwise
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hpointwise : PositivePhysicalConnectedRawPointwiseCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact coarseGibbsRefreshConnectedRemainderCalibration_of_sourceL1
    S hfineCutoff hcoarseCoupling M g kernelCeiling
    (coarseGibbsRefreshConnectedSourceL1Calibration_of_positiveRawPointwise
      S hfineCutoff hcoarseCoupling M g kernelCeiling hpointwise)

#print axioms wholeSlabRecouplingRawObservableNumerator
#print axioms wholeSlabRecouplingRawObservableRatio
#print axioms conditionalKernelObservableExpectation_eqv_rawRatio
#print axioms positivePhysicalConnectedRawRowAction
#print axioms coarseGibbsRefreshConnectedRowAction_eqv_positiveRaw
#print axioms positivePhysicalConnectedRawSignedSourceAverageAux
#print axioms positivePhysicalConnectedRawSignedSourceAverage
#print axioms coarseGibbsRefreshConnectedSignedSourceAverage_eqv_positiveRaw
#print axioms positivePhysicalConnectedRawSignedSourceAverage_eqv_centeredRemainder
#print axioms positivePhysicalConnectedRawSourceL1Aux
#print axioms positivePhysicalConnectedRawSourceL1
#print axioms coarseGibbsRefreshConnectedSourceL1_eqv_positiveRaw
#print axioms PositivePhysicalConnectedRawSignedSourceAverageCalibration
#print axioms PositivePhysicalConnectedRawSourceL1Calibration
#print axioms PositivePhysicalConnectedRawPointwiseCalibration
#print axioms positiveRawSignedSourceAverageCalibration_iff_centeredRemainder
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawSourceL1
#print axioms coarseGibbsRefreshConnectedSourceL1Calibration_of_positiveRawPointwise
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawPointwise

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
