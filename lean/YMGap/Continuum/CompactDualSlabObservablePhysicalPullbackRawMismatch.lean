/-
# Raw-weight disintegration of the actual physical pullback mismatch

The geometric mismatch cost is defined for an abstract finite slab kernel.
This module identifies it for the actual cutoff-one globally link-glued
recoupling kernel.  On every strictly positive fine Gibbs row, the mismatch
mass is exactly

  selected mismatch raw weight / complete row raw partition.

Rows whose fine physical summand is not strictly positive have exactly zero
normalized fine mass, so their contribution to the averaged mismatch is
zero.  A dependent finite recursion removes those null rows and leaves an
explicit positive-row sum of normalized fine masses times raw mismatch
ratios.  The root, target, and joint costs are then assembled for the literal
face covariance.

This is an exact finite identity, not a smallness or decay estimate.  Its
purpose is to expose the globally glued face-product and link-multiplicity raw
weights to the next geometric bound.

Constructive contract: finite exact-rational sums and the existing explicit
recoupling kernel only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One positive row as a selected raw-weight ratio -/

/-- Raw recoupling mass selected by one Boolean coarse event. -/
def wholeSlabRecouplingRawCylinderMass
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  finiteEventMass
    (wholeSlabRecouplingRawWeight S source.fineState)
    S.coarse.physicalLabellings event

/-- Selected raw event mass divided by the complete positive row partition. -/
def wholeSlabRecouplingRawCylinderRatio
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  Q'.divPos
    (wholeSlabRecouplingRawCylinderMass source event)
    (wholeSlabRecouplingPartition source)
    (wholeSlabRecouplingPartition_pos source)

/-- Event mass under a positive conditional recoupling row is exactly its
selected raw numerator divided by the complete row partition. -/
theorem conditionalKernelCylinderMass_eqv_rawCylinderRatio
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (event : EdgeLabelling → Bool) :
    finiteEventMass
        (wholeSlabRecouplingConditionalKernel source)
        S.coarse.physicalLabellings event ≈
      wholeSlabRecouplingRawCylinderRatio source event := by
  unfold finiteEventMass wholeSlabRecouplingConditionalKernel
    wholeSlabRecouplingRawCylinderRatio
    wholeSlabRecouplingRawCylinderMass Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (if event target then
          wholeSlabRecouplingRawWeight S source.fineState target
        else 0) *
          Q'.recipPos (wholeSlabRecouplingPartition source)
            (wholeSlabRecouplingPartition_pos source))
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    cases hevent : event target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv
          (Q'.recipPos (wholeSlabRecouplingPartition source)
            (wholeSlabRecouplingPartition_pos source)))
    · simp only [if_true]
      exact Q'.eqv_refl _
  exact listQSum_mul_right
    (fun target =>
      if event target then
        wholeSlabRecouplingRawWeight S source.fineState target
      else 0)
    (Q'.recipPos (wholeSlabRecouplingPartition source)
      (wholeSlabRecouplingPartition_pos source))
    S.coarse.physicalLabellings

/-- The explicit positive-row raw mismatch ratio for the actual cutoff-one
physical kernel. -/
def positivePhysicalRawMismatchRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  wholeSlabRecouplingRawCylinderRatio
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source)

/-- On a strictly positive fine Gibbs row, the actual kernel mismatch mass is
the selected globally glued raw mismatch ratio. -/
theorem physicalKernelRowMismatchMass_eqv_positiveRawRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    kernelRowCylinderMismatchMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        fineEvent coarseEvent source ≈
      positivePhysicalRawMismatchRatio S hfineCutoff hcoarseCoupling
        source hsource hpositive fineEvent coarseEvent := by
  unfold kernelRowCylinderMismatchMass physicalKernel
    positivePhysicalRawMismatchRatio
  refine Q'.eqv_trans _
    (finiteEventMass
      (wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          source hsource hpositive))
      S.coarse.physicalLabellings
      (cylinderPullbackMismatchEvent
        fineEvent coarseEvent source)) _ ?_ ?_
  · unfold finiteEventMass
    apply listQSum_congr_on
    intro target _
    cases hmismatch :
        cylinderPullbackMismatchEvent fineEvent coarseEvent source target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
    · simp only [if_true]
      exact cutoffOneWholeSlabKernel_eq_positive
        S hfineCutoff hcoarseCoupling hsource hpositive target
  exact conditionalKernelCylinderMass_eqv_rawCylinderRatio
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source)

/-! ## 2. Remove Gibbs-null rows from the mismatch average -/

/-- Positive-row recursion for the actual averaged raw mismatch.  Membership
is carried as data so each positive branch constructs its coherent source
without choice. -/
def physicalRawMismatchAverageAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        S.fine.normalizedMass source *
            positivePhysicalRawMismatchRatio S hfineCutoff
              hcoarseCoupling source
              (hphysical source List.mem_cons_self) hpositive
              fineEvent coarseEvent +
          physicalRawMismatchAverageAux S hfineCutoff
            hcoarseCoupling fineEvent coarseEvent tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        physicalRawMismatchAverageAux S hfineCutoff
          hcoarseCoupling fineEvent coarseEvent tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- Complete actual positive-row raw mismatch average. -/
def physicalRawMismatchAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  physicalRawMismatchAverageAux S hfineCutoff hcoarseCoupling
    fineEvent coarseEvent S.fine.physicalLabellings
    (fun _ hsource => hsource)

private theorem physicalMismatchSum_eq_rawAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              kernelRowCylinderMismatchMass
                (physicalKernel S hfineCutoff hcoarseCoupling)
                fineEvent coarseEvent source)
          sources ≈
        physicalRawMismatchAverageAux S hfineCutoff hcoarseCoupling
          fineEvent coarseEvent sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, physicalRawMismatchAverageAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (physicalKernelRowMismatchMass_eqv_positiveRawRatio
              S hfineCutoff hcoarseCoupling source hsource hpositive
              fineEvent coarseEvent))
          (physicalMismatchSum_eq_rawAux S hfineCutoff hcoarseCoupling
            fineEvent coarseEvent tail htail)
      · simp only [listQSum, physicalRawMismatchAverageAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + physicalRawMismatchAverageAux S hfineCutoff
            hcoarseCoupling fineEvent coarseEvent tail htail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * kernelRowCylinderMismatchMass
                (physicalKernel S hfineCutoff hcoarseCoupling)
                fineEvent coarseEvent source) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv _))
            (physicalMismatchSum_eq_rawAux S hfineCutoff hcoarseCoupling
              fineEvent coarseEvent tail htail)
        exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The generic mismatch average of the actual physical kernel is exactly the
positive-row globally glued raw mismatch average. -/
theorem averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    averagedCylinderPullbackMismatchMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        fineEvent coarseEvent ≈
      physicalRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineEvent coarseEvent := by
  unfold averagedCylinderPullbackMismatchMass
    physicalRawMismatchAverage
  exact physicalMismatchSum_eq_rawAux S hfineCutoff hcoarseCoupling
    fineEvent coarseEvent S.fine.physicalLabellings
    (fun _ hsource => hsource)

/-! ## 3. Actual raw mismatch cost for the literal face covariance -/

def physicalFaceRawMismatchAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineFaceId coarseFaceId : Nat) : Q' :=
  physicalRawMismatchAverage S hfineCutoff hcoarseCoupling
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

def physicalFacePairRawMismatchAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  physicalRawMismatchAverage S hfineCutoff hcoarseCoupling
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- Root/target/joint mismatch cost written entirely through the actual
globally link-glued recoupling raw weights. -/
def physicalObservableRawMismatchCost
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  physicalFacePairRawMismatchAverage S hfineCutoff hcoarseCoupling
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget +
    (physicalFaceRawMismatchAverage S hfineCutoff hcoarseCoupling
        M.fineRoot M.coarseRoot +
      physicalFaceRawMismatchAverage S hfineCutoff hcoarseCoupling
        M.fineTarget M.coarseTarget)

/-- The geometric mismatch cost consumed by the covariance theorem is exactly
the explicit actual-kernel positive-row raw mismatch cost. -/
theorem observableSourcePullbackMismatchCost_physicalKernel_eqv_raw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    observableSourcePullbackMismatchCost
        (physicalKernel S hfineCutoff hcoarseCoupling) M ≈
      physicalObservableRawMismatchCost S hfineCutoff
        hcoarseCoupling M := by
  unfold observableSourcePullbackMismatchCost
    facePairSourcePullbackMismatchMass
    faceSourcePullbackMismatchMass
    physicalObservableRawMismatchCost
    physicalFacePairRawMismatchAverage
    physicalFaceRawMismatchAverage
  exact Q'.add_eqv_congr'
    (averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
      S hfineCutoff hcoarseCoupling
      (slabPhysicalFacePairPositiveB M.fineRoot M.fineTarget)
      (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget))
    (Q'.add_eqv_congr'
      (averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
        S hfineCutoff hcoarseCoupling
        (slabPhysicalFacePositiveB M.fineRoot)
        (slabPhysicalFacePositiveB M.coarseRoot))
      (averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
        S hfineCutoff hcoarseCoupling
        (slabPhysicalFacePositiveB M.fineTarget)
        (slabPhysicalFacePositiveB M.coarseTarget)))

#print axioms wholeSlabRecouplingRawCylinderMass
#print axioms wholeSlabRecouplingRawCylinderRatio
#print axioms conditionalKernelCylinderMass_eqv_rawCylinderRatio
#print axioms positivePhysicalRawMismatchRatio
#print axioms physicalKernelRowMismatchMass_eqv_positiveRawRatio
#print axioms physicalRawMismatchAverageAux
#print axioms physicalRawMismatchAverage
#print axioms averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
#print axioms physicalFaceRawMismatchAverage
#print axioms physicalFacePairRawMismatchAverage
#print axioms physicalObservableRawMismatchCost
#print axioms observableSourcePullbackMismatchCost_physicalKernel_eqv_raw

end YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
