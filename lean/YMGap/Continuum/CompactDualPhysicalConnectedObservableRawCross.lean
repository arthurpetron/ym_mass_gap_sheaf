/-
# Raw cross form of the connected physical observable defect

The sharp connected pushed-law remainder is already the matching defect of
one explicit unit-bounded observable.  This module clears both normalizations.
It writes the blocked expectation as a raw fine-partition numerator and the
coarse expectation as a raw coarse-partition numerator, then identifies their
difference with the cross determinant divided by the product partition.

The resulting cross determinant is the next analytic object: an `O(a)` bound
on it relative to the product partition gives the required normalized
connected estimate.  No such bound is proved here, and no continuum measure,
OS/GNS reconstruction, or physical mass gap is inferred.

Constructive contract: finite rational sums, exact positive-denominator
division, and the actual finite physical kernel only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable

namespace YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Raw observable numerators -/

/-- Unnormalized physical expectation numerator for an arbitrary rational
observable on one corrected slab. -/
def physicalObservableNumerator
    (D : SlabPhysicalData) (observable : SlabLabelling → Q') : Q' :=
  listQSum
    (fun state => D.physicalTerm state * observable state)
    D.physicalLabellings

/-- Raw numerator obtained by applying the actual finite block kernel to an
observable before normalizing the fine Gibbs law. -/
def pushedPhysicalObservableNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') : Q' :=
  listQSum
    (fun source =>
      S.fine.physicalTerm source *
        listQSum
          (fun target => K.kernel source target * observable target)
          S.coarse.physicalLabellings)
    S.fine.physicalLabellings

/-- A normalized physical expectation is its literal raw numerator divided
by the positive physical partition. -/
theorem normalizedObservableExpectation_eqv_raw_divPos
    (D : SlabPhysicalData) (observable : SlabLabelling → Q') :
    observableExpectation D.normalizedMass D.physicalLabellings observable ≈
      Q'.divPos
        (physicalObservableNumerator D observable)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent) := by
  let reciprocal := Q'.recipPos D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
  unfold observableExpectation SlabPhysicalData.normalizedMass Q'.divPos
    physicalObservableNumerator
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (D.physicalTerm state * observable state) * reciprocal)
      D.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ D.physicalLabellings
      (fun state _ => by
        unfold reciprocal
        ring_qeqv)
  exact listQSum_mul_const
    (fun state => D.physicalTerm state * observable state)
    reciprocal D.physicalLabellings

/-! ## 2. The pushed numerator really clears the fine normalization -/

/-- The blocked observable expectation is the raw pushed numerator divided by
the fine physical partition. -/
theorem blockedObservableExpectation_eqv_pushedRaw_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') :
    observableExpectation K.blockedMass S.coarse.physicalLabellings
        observable ≈
      Q'.divPos
        (pushedPhysicalObservableNumerator K observable)
        S.fine.physicalPartition
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent) := by
  let reciprocal := Q'.recipPos S.fine.physicalPartition
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  let kernelAverage := fun source =>
    listQSum
      (fun target => K.kernel source target * observable target)
      S.coarse.physicalLabellings
  unfold observableExpectation SlabScalePair.FiniteSlabKernel.blockedMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            (S.fine.normalizedMass source * K.kernel source target) *
              observable target)
          S.fine.physicalLabellings)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _ =>
        Q'.eqv_symm
          (listQSum_mul_const
            (fun source =>
              S.fine.normalizedMass source * K.kernel source target)
            (observable target) S.fine.physicalLabellings))
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (S.fine.normalizedMass source * K.kernel source target) *
              observable target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        (S.fine.normalizedMass source * K.kernel source target) *
          observable target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun source => S.fine.normalizedMass source * kernelAverage source)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.fine.physicalLabellings
      (fun source _ => by
        unfold kernelAverage
        refine Q'.eqv_trans _
          (listQSum
            (fun target =>
              S.fine.normalizedMass source *
                (K.kernel source target * observable target))
            S.coarse.physicalLabellings) _ ?_ ?_
        · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
            (fun target _ =>
              Q'.mul_assoc_eqv
                (S.fine.normalizedMass source)
                (K.kernel source target) (observable target))
        exact listQSum_mul_left
          (S.fine.normalizedMass source)
          (fun target => K.kernel source target * observable target)
          S.coarse.physicalLabellings)
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (S.fine.physicalTerm source * kernelAverage source) * reciprocal)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.fine.physicalLabellings
      (fun source _ => by
        unfold SlabPhysicalData.normalizedMass Q'.divPos reciprocal
        ring_qeqv)
  refine Q'.eqv_trans _
    (pushedPhysicalObservableNumerator K observable * reciprocal) _ ?_ ?_
  · exact listQSum_mul_const
      (fun source => S.fine.physicalTerm source * kernelAverage source)
      reciprocal S.fine.physicalLabellings
  unfold Q'.divPos pushedPhysicalObservableNumerator reciprocal
  exact Q'.eqv_refl _

/-! ## 3. Cross determinant for the normalized matching defect -/

/-- Division-free cross determinant of the blocked and coarse observable
numerators. -/
def physicalObservableRawCrossDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') : Q' :=
  pushedPhysicalObservableNumerator K observable *
      S.coarse.physicalPartition +
    -(physicalObservableNumerator S.coarse observable *
      S.fine.physicalPartition)

/-- Exact normalization identity: the finite-kernel matching defect is the
absolute raw cross determinant divided by the product physical partition. -/
theorem finiteKernelObservableMatchDefect_eqv_rawCross_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') :
    finiteKernelObservableMatchDefect K observable ≈
      Q'.abs
        (Q'.divPos
          (physicalObservableRawCrossDefect K observable)
          (S.fine.physicalPartition * S.coarse.physicalPartition)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
            (slabParametricKPhysicalPartition_pos
              S.coarse.coupling_nonnegative S.coarse.cutoff
              S.coarse.extent))) := by
  let hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  unfold finiteKernelObservableMatchDefect
  apply Q'.abs_eqv_congr
  refine Q'.eqv_trans _
    (Q'.divPos (pushedPhysicalObservableNumerator K observable)
        S.fine.physicalPartition hfine +
      -(Q'.divPos (physicalObservableNumerator S.coarse observable)
        S.coarse.physicalPartition hcoarse)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (blockedObservableExpectation_eqv_pushedRaw_divPos K observable)
      (Q'.neg_eqv_congr _ _
        (normalizedObservableExpectation_eqv_raw_divPos
          S.coarse observable))
  simpa only [physicalObservableRawCrossDefect] using
    (divPos_sub_divPos_eq_crossDifference
      (pushedPhysicalObservableNumerator K observable)
      (physicalObservableNumerator S.coarse observable)
      S.fine.physicalPartition S.coarse.physicalPartition
      hfine hcoarse)

/-- The sharp connected remainder is therefore the normalized absolute raw
cross determinant of its explicit structured observable. -/
theorem connectedRemainder_abs_eqv_rawCross_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    Q'.abs (centeredCylinderRemainder K M) ≈
      Q'.abs
        (Q'.divPos
          (physicalObservableRawCrossDefect K
            (connectedRemainderObservable K M))
          (S.fine.physicalPartition * S.coarse.physicalPartition)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
            (slabParametricKPhysicalPartition_pos
              S.coarse.coupling_nonnegative S.coarse.cutoff
              S.coarse.extent))) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (connectedObservableMatchDefect_eqv_abs_centeredCylinderRemainder
        K M))
    (finiteKernelObservableMatchDefect_eqv_rawCross_divPos K
      (connectedRemainderObservable K M))

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross :
        -(budget * denominator) ≤ -(Q'.abs numerator) :=
      Q'.neg_le_neg hcross
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hcross

/-- Division-free analytic input for the connected producer.  It is enough to
bound the absolute raw cross determinant by `budget` times the exact product
partition; normalization then gives the required connected bound. -/
theorem connectedRemainder_abs_le_of_rawCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalObservableRawCrossDefect K
            (connectedRemainderObservable K M)) ≤
        budget *
          (S.fine.physicalPartition * S.coarse.physicalPartition)) :
    Q'.abs (centeredCylinderRemainder K M) ≤ budget := by
  let hproduct := Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (connectedRemainder_abs_eqv_rawCross_divPos K M)) ?_
  exact abs_divPos_le_of_abs_le_mul_local hproduct hcross

#print axioms physicalObservableNumerator
#print axioms pushedPhysicalObservableNumerator
#print axioms normalizedObservableExpectation_eqv_raw_divPos
#print axioms blockedObservableExpectation_eqv_pushedRaw_divPos
#print axioms physicalObservableRawCrossDefect
#print axioms finiteKernelObservableMatchDefect_eqv_rawCross_divPos
#print axioms connectedRemainder_abs_eqv_rawCross_divPos
#print axioms connectedRemainder_abs_le_of_rawCross

end YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
