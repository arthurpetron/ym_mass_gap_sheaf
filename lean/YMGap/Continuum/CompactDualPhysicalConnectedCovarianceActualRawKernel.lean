/-
# Global-normalization-free covariance for the actual recoupling kernel

The normalized face moments have already been cleared into raw event
numerators.  This module now specializes the pushed numerators to the actual
cutoff-one globally link-glued physical kernel.  Gibbs-null fine rows are
removed constructively, and every positive row contributes its literal fine
physical term times a selected whole-slab recoupling raw-weight ratio.

The resulting connected covariance cross is an explicit finite expression in
the production kernel data.  A relative bound on it still remains open; this
module is an exact reduction, not an asymptotic estimate, continuum measure,
OS/GNS reconstruction, or mass-gap theorem.

Constructive contract: dependent finite rational recursion and the existing
globally glued row weights only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Positive-row raw event ratios -/

/-- The literal selected raw event ratio in one positive fine Gibbs row. -/
def positivePhysicalRawEventRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (event : EdgeLabelling → Bool) : Q' :=
  wholeSlabRecouplingRawCylinderRatio
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    event

/-- A weighted Boolean indicator sum is its finite event mass. -/
private theorem rowIndicatorSum_eqv_eventMass
    (mass : EdgeLabelling → Q') (states : List EdgeLabelling)
    (event : EdgeLabelling → Bool) :
    listQSum
        (fun state =>
          mass state * weightedCylinderObservable event 1 state)
        states ≈
      finiteEventMass mass states event := by
  unfold weightedCylinderObservable finiteEventMass
  exact listQSum_congr_on _ _ states
    (fun state _ => by
      cases hevent : event state
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.mul_zero_eqv (mass state)
      · simp only [if_true]
        exact Q'.mul_one_eqv (mass state))

/-- An arbitrary event mass in a positive row of the actual physical kernel
is its selected globally glued raw numerator divided by the complete row
partition. -/
theorem physicalKernelRowEventMass_eqv_positiveRawRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (event : EdgeLabelling → Bool) :
    finiteEventMass
        ((physicalKernel S hfineCutoff hcoarseCoupling).kernel source)
        S.coarse.physicalLabellings event ≈
      positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
        source hsource hpositive event := by
  unfold physicalKernel positivePhysicalRawEventRatio
  refine Q'.eqv_trans _
    (finiteEventMass
      (wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          source hsource hpositive))
      S.coarse.physicalLabellings event) _ ?_ ?_
  · unfold finiteEventMass
    apply listQSum_congr_on
    intro target _
    cases hevent : event target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
    · simp only [if_true]
      exact cutoffOneWholeSlabKernel_eq_positive
        S hfineCutoff hcoarseCoupling hsource hpositive target
  · exact conditionalKernelCylinderMass_eqv_rawCylinderRatio
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source hsource hpositive)
      event

/-! ## 2. Remove null rows from the pushed raw numerator -/

/-- Dependent positive-row recursion for one actual pushed raw event
numerator. -/
def actualPushedPhysicalEventNumeratorAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (event : EdgeLabelling → Bool) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        S.fine.physicalTerm source *
            positivePhysicalRawEventRatio S hfineCutoff
              hcoarseCoupling source
              (hphysical source List.mem_cons_self) hpositive event +
          actualPushedPhysicalEventNumeratorAux S hfineCutoff
            hcoarseCoupling event tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        actualPushedPhysicalEventNumeratorAux S hfineCutoff
          hcoarseCoupling event tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- The complete actual pushed raw event numerator, with Gibbs-null rows
omitted and every positive row written through literal recoupling weights. -/
def actualPushedPhysicalEventNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (event : EdgeLabelling → Bool) : Q' :=
  actualPushedPhysicalEventNumeratorAux S hfineCutoff hcoarseCoupling
    event S.fine.physicalLabellings (fun _ hsource => hsource)

private theorem pushedEventSum_eqv_actualAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (event : EdgeLabelling → Bool) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.physicalTerm source *
              listQSum
                (fun target =>
                  (physicalKernel S hfineCutoff hcoarseCoupling).kernel
                      source target *
                    weightedCylinderObservable event 1 target)
                S.coarse.physicalLabellings)
          sources ≈
        actualPushedPhysicalEventNumeratorAux S hfineCutoff
          hcoarseCoupling event sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, actualPushedPhysicalEventNumeratorAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.physicalTerm source) _ _
            (Q'.eqv_trans _ _ _
              (rowIndicatorSum_eqv_eventMass
                ((physicalKernel S hfineCutoff hcoarseCoupling).kernel
                  source)
                S.coarse.physicalLabellings event)
              (physicalKernelRowEventMass_eqv_positiveRawRatio
                S hfineCutoff hcoarseCoupling source hsource hpositive
                event)))
          (pushedEventSum_eqv_actualAux S hfineCutoff
            hcoarseCoupling event tail htail)
      · simp only [listQSum, actualPushedPhysicalEventNumeratorAux,
          dif_neg hpositive]
        let rowAverage :=
          listQSum
            (fun target =>
              (physicalKernel S hfineCutoff hcoarseCoupling).kernel
                  source target *
                weightedCylinderObservable event 1 target)
            S.coarse.physicalLabellings
        refine Q'.eqv_trans _
          (0 + actualPushedPhysicalEventNumeratorAux S hfineCutoff
            hcoarseCoupling event tail htail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _ (0 * rowAverage) _
              (Q'.mul_eqv_congr_right _ _ rowAverage
                (physicalTerm_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv rowAverage))
            (pushedEventSum_eqv_actualAux S hfineCutoff
              hcoarseCoupling event tail htail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The generic pushed raw numerator, specialized to the actual physical
kernel, is exactly the positive-row globally glued raw expression. -/
theorem pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (event : EdgeLabelling → Bool) :
    pushedPhysicalEventNumerator
        (physicalKernel S hfineCutoff hcoarseCoupling) event ≈
      actualPushedPhysicalEventNumerator S hfineCutoff
        hcoarseCoupling event := by
  unfold pushedPhysicalEventNumerator
    actualPushedPhysicalEventNumerator
  exact pushedEventSum_eqv_actualAux S hfineCutoff hcoarseCoupling
    event S.fine.physicalLabellings (fun _ hsource => hsource)

/-! ## 3. The actual fully raw covariance cross -/

private theorem rawCovarianceNumerator_eqv_of_eqv
    {joint joint' root root' target target' partition : Q'}
    (hjoint : joint ≈ joint') (hroot : root ≈ root')
    (htarget : target ≈ target') :
    rawCovarianceNumerator joint root target partition ≈
      rawCovarianceNumerator joint' root' target' partition := by
  unfold rawCovarianceNumerator
  exact sub_eqv_both_local
    (Q'.mul_eqv_congr_right _ _ (partition * partition) hjoint)
    (Q'.mul_eqv_congr_right _ _ partition
      (mul_eqv_both_local hroot htarget))

/-- The pushed raw covariance numerator of the actual physical kernel, using
only positive-row recoupling raw event ratios. -/
def actualPushedFaceRawCovarianceNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  rawCovarianceNumerator
    (actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
      (slabPhysicalFacePairPositiveB root target))
    (actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
      (slabPhysicalFacePositiveB root))
    (actualPushedPhysicalEventNumerator S hfineCutoff hcoarseCoupling
      (slabPhysicalFacePositiveB target))
    S.fine.physicalPartition

theorem pushedFaceRawCovarianceNumerator_physicalKernel_eqv_actualRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    pushedFaceRawCovarianceNumerator
        (physicalKernel S hfineCutoff hcoarseCoupling) root target ≈
      actualPushedFaceRawCovarianceNumerator S hfineCutoff
        hcoarseCoupling root target := by
  unfold pushedFaceRawCovarianceNumerator
    actualPushedFaceRawCovarianceNumerator
  exact rawCovarianceNumerator_eqv_of_eqv
    (pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
      S hfineCutoff hcoarseCoupling _)
    (pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
      S hfineCutoff hcoarseCoupling _)
    (pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
      S hfineCutoff hcoarseCoupling _)

/-- Global-normalization-free connected covariance determinant for the actual
globally link-glued physical kernel.  Its conditional rows remain literal raw
event-weight ratios. -/
def physicalConnectedCovarianceRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  coarseFaceRawCovarianceNumerator
      S.coarse M.coarseRoot M.coarseTarget *
      rawCovarianceDenominator S.fine.physicalPartition -
    actualPushedFaceRawCovarianceNumerator
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    connectedCovarianceRawCrossDefect
        (physicalKernel S hfineCutoff hcoarseCoupling) M ≈
      physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M := by
  unfold connectedCovarianceRawCrossDefect
    physicalConnectedCovarianceRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _ _
      (pushedFaceRawCovarianceNumerator_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget))

/-- A relative estimate of the actual positive-row raw determinant is enough
for the exact connected pushed-law remainder bound. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_actualRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovarianceRawCrossDefect S hfineCutoff
            hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_abs_le_of_covarianceRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms positivePhysicalRawEventRatio
#print axioms physicalKernelRowEventMass_eqv_positiveRawRatio
#print axioms actualPushedPhysicalEventNumeratorAux
#print axioms actualPushedPhysicalEventNumerator
#print axioms pushedPhysicalEventNumerator_physicalKernel_eqv_actualRaw
#print axioms actualPushedFaceRawCovarianceNumerator
#print axioms pushedFaceRawCovarianceNumerator_physicalKernel_eqv_actualRaw
#print axioms physicalConnectedCovarianceRawCrossDefect
#print axioms connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_actualRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
