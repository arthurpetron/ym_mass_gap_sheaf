/-
# Every positive cutoff-one source row as a normalized lowering law

Every cutoff-one fine physical source supplies four binary fine spins over
each coarse face.  Their total defines a coarse source labelling.  The local
placement-independence theorem identifies the corresponding face row with the
canonical spin-four lowering row indexed by that total.

This file lifts that identity through the complete face product and the
unchanged shared-link multiplicity, restricts the raw row to its exact global
lowering downset, factors it as an integer tilt of coarse Gibbs mass, and
normalizes it.  The final theorem applies to every proof-carrying positive
fine source used by the signed observable path expansion.

Constructive contract: exact finite sums/products, decidable SU(2) fusion,
and positive rational division only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryPacketLoweringKernel
import YMGap.Continuum.Z4DyadicSpinFourLoweringConditionalLaw

namespace YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryPacketLoweringKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The facewise total-spin source labelling -/

/-- The coarse face label obtained by retaining the total number of
fundamental fine strands in that face's dyadic fibre. -/
def wholeSlabFinePacketTotalLabelling
    (S : SlabScalePair) (fineState : EdgeLabelling) : EdgeLabelling :=
  fun faceId =>
    faceSpinPacketTotal (wholeSlabFinePacket S fineState faceId)

/-- Every packet extracted from a cutoff-one fine physical source is
pointwise binary. -/
theorem wholeSlabFinePacket_binary
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (faceId : Nat) :
    PacketBinary (wholeSlabFinePacket S fineState faceId) := by
  have hpacket := (mem_faceSpinPacketStateSpace_iff
    S.fine.cutoff (wholeSlabFinePacket S fineState faceId)).mp
      (wholeSlabFinePacket_mem hfineMem faceId)
  rw [hfineCutoff] at hpacket
  exact hpacket

/-- The induced total-spin source is bounded by the lossless coarse cutoff
on every physical coarse face. -/
theorem wholeSlabFinePacketTotalLabelling_le_four
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (faceId : Nat) (_hface : faceId ∈ S.coarse.faceEdges) :
    wholeSlabFinePacketTotalLabelling S fineState faceId ≤ 4 := by
  exact faceSpinPacketTotal_le_four_of_binary
    (wholeSlabFinePacket_binary S hfineCutoff hfineMem faceId)

private theorem coarse_target_spin_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId ≤ 4 := by
  have htargetSound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htargetMem
  have hbound := Nat.le_of_lt_succ (htargetSound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-! ## 2. Lift the arbitrary binary packet through the whole slab -/

/-- One arbitrary cutoff-one fine face has exactly the canonical lowering
weight indexed by its packet total. -/
theorem wholeSlabFaceRawWeight_eqv_totalLoweringFaceWeight
    (S : SlabScalePair) (fineState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    wholeSlabFaceRawWeight S fineState targetState faceId ≈
      spinFourLoweringFaceWeight S.coarse.coupling
        (wholeSlabFinePacketTotalLabelling S fineState faceId)
        (targetState faceId) := by
  unfold wholeSlabFaceRawWeight spinFourLoweringFaceWeight
  rw [hfineCutoff]
  exact binaryPacket_fixedFinalFaceRawWeight_eqv_spinFourMultiplicity
    S.coarse.coupling (wholeSlabFinePacket S fineState faceId)
      (targetState faceId)
      (wholeSlabFinePacket_binary S hfineCutoff hfineMem faceId)
      (coarse_target_spin_le_four S hfineCutoff htargetMem faceId hface)

private theorem wholeSlabFiniteQProduct_congr_on_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      wholeSlabFiniteQProduct left items ≈
        wholeSlabFiniteQProduct right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      change
        left head * wholeSlabFiniteQProduct left tail ≈
          right head * wholeSlabFiniteQProduct right tail
      exact Q'.eqv_trans _
        (right head * wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_on_local left right tail
            (fun item hmem =>
              hagree item (List.mem_cons_of_mem head hmem))))

/-- The complete globally link-glued raw transition of every cutoff-one fine
physical source is its total-spin lower-triangular row. -/
theorem wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
    (S : SlabScalePair) (fineState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingRawWeight S fineState targetState ≈
      spinFourLoweringWholeSlabRawWeight S
        (wholeSlabFinePacketTotalLabelling S fineState) targetState := by
  let linkFactor : Q' := Q'.ofNat
    (slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent targetState)
  have hfaceProduct :
      wholeSlabFaceRawProduct S fineState targetState ≈
        wholeSlabFiniteQProduct
          (fun faceId =>
            spinFourLoweringFaceWeight S.coarse.coupling
              (wholeSlabFinePacketTotalLabelling S fineState faceId)
              (targetState faceId))
          S.coarse.faceEdges := by
    exact Q'.eqv_trans _
      (wholeSlabFiniteQProduct
        (wholeSlabFaceRawWeight S fineState targetState)
        S.coarse.faceEdges) _
      (wholeSlabFaceRawProduct_eqv_finiteQProduct
        S fineState targetState)
      (wholeSlabFiniteQProduct_congr_on_local _ _ _
        (fun faceId hface =>
          wholeSlabFaceRawWeight_eqv_totalLoweringFaceWeight
            S fineState targetState hfineCutoff hfineMem htargetMem
              faceId hface))
  unfold wholeSlabRecouplingRawWeight
    spinFourLoweringWholeSlabRawWeight
  change wholeSlabFaceRawProduct S fineState targetState * linkFactor ≈
    wholeSlabFiniteQProduct
        (fun faceId =>
          spinFourLoweringFaceWeight S.coarse.coupling
            (wholeSlabFinePacketTotalLabelling S fineState faceId)
            (targetState faceId))
        S.coarse.faceEdges * linkFactor
  exact Q'.mul_eqv_congr_right _ _ linkFactor hfaceProduct

/-! ## 3. Exact all-source row mass -/

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false → value item ≈ 0) →
      listQSum value source ≈ listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

/-- The complete raw row mass of every cutoff-one fine physical source is an
integer-tilted coarse Gibbs mass over its own exact lowering downset. -/
theorem wholeSlabRawRowMass_eqv_totalMultiplicityTiltedGibbs
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    listQSum (wholeSlabRecouplingRawWeight S fineState)
        S.coarse.physicalLabellings ≈
      listQSum
        (fun targetState =>
          Q'.ofNat
              (spinFourLoweringMultiplicityProduct S
                (wholeSlabFinePacketTotalLabelling S fineState)
                targetState) *
            S.coarse.physicalTerm targetState)
        (spinFourLoweringTargets S
          (wholeSlabFinePacketTotalLabelling S fineState)) := by
  let sourceState := wholeSlabFinePacketTotalLabelling S fineState
  let loweringWeight :=
    spinFourLoweringWholeSlabRawWeight S sourceState
  have hsource : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      sourceState faceId ≤ 4 := by
    intro faceId hface
    exact wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff hfineMem faceId hface
  refine Q'.eqv_trans _
    (listQSum loweringWeight S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro targetState htargetMem
    exact wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
      S fineState targetState hfineCutoff hfineMem htargetMem
  refine Q'.eqv_trans _
    (listQSum loweringWeight
      (spinFourLoweringTargets S sourceState)) _ ?_ ?_
  · unfold spinFourLoweringTargets
    apply listQSum_eq_filter_of_zero_local
    intro targetState htargetMem htest
    exact spinFourLoweringWholeSlabRawWeight_eqv_zero_of_test_false
      S sourceState targetState hfineCutoff hsource htargetMem htest
  · apply listQSum_congr_on
    intro targetState htarget
    exact spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
      S sourceState targetState
        ((mem_spinFourLoweringTargets_iff
          S sourceState targetState).mp htarget).1

/-! ## 4. Normalize every positive fine-source row -/

/-- The actual coherent recoupling source attached to an arbitrary positive
fine physical source. -/
def positivePhysicalSourceCoherentSource
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    source.1 source.2.1 source.2.2

/-- The source-dependent integer-tilted Gibbs normalization. -/
def positivePhysicalSourceTiltedGibbsRowMass
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Q' :=
  listQSum
    (fun targetState =>
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct S
            (wholeSlabFinePacketTotalLabelling S source.1)
            targetState) *
        S.coarse.physicalTerm targetState)
    (spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1))

/-- The coherent recoupling denominator is exactly the source-dependent
tilted Gibbs row mass. -/
theorem wholeSlabRecouplingPartition_positivePhysicalSource_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    wholeSlabRecouplingPartition
        (positivePhysicalSourceCoherentSource
          S hfineCutoff hcoarseCoupling source) ≈
      positivePhysicalSourceTiltedGibbsRowMass S source := by
  unfold wholeSlabRecouplingPartition
    positivePhysicalSourceCoherentSource
    positivePhysicalSourceTiltedGibbsRowMass
  exact wholeSlabRawRowMass_eqv_totalMultiplicityTiltedGibbs
    S source.1 hfineCutoff source.2.1

/-- Every displayed all-source tilted row mass is strictly positive. -/
theorem positivePhysicalSourceTiltedGibbsRowMass_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    (0 : Q') < positivePhysicalSourceTiltedGibbsRowMass S source := by
  have hpartition := wholeSlabRecouplingPartition_pos
    (positivePhysicalSourceCoherentSource
      S hfineCutoff hcoarseCoupling source)
  have heq :=
    wholeSlabRecouplingPartition_positivePhysicalSource_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling source
  exact Q'.pos_of_lt_of_le hpartition (Q'.le_of_eqv heq)

private theorem divPos_eqv_congr_local
    {numerator numerator' denominator denominator' : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominator' : (0 : Q') < denominator')
    (hnumerator : numerator ≈ numerator')
    (hdenominatorEq : denominator ≈ denominator') :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator' denominator' hdenominator' := by
  apply Q'.eqv_of_le_le
  · apply Q'.le_divPos_of_mul_le
      numerator' denominator' hdenominator'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator hdenominator)
          denominator' denominator
          (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le
      numerator denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator' hdenominator')
          denominator denominator' hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator' denominator' hdenominator')
          (Q'.eqv_symm hnumerator)))

/-- Every coherent positive-source conditional row is the normalized
integer-tilted Gibbs law determined by its facewise packet totals. -/
theorem wholeSlabRecouplingConditionalKernel_positivePhysicalSource_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingConditionalKernel
        (positivePhysicalSourceCoherentSource
          S hfineCutoff hcoarseCoupling source) targetState ≈
      Q'.divPos
        (Q'.ofNat
            (spinFourLoweringMultiplicityProduct S
              (wholeSlabFinePacketTotalLabelling S source.1)
              targetState) *
          S.coarse.physicalTerm targetState)
        (positivePhysicalSourceTiltedGibbsRowMass S source)
        (positivePhysicalSourceTiltedGibbsRowMass_pos
          S hfineCutoff hcoarseCoupling source) := by
  let coherent := positivePhysicalSourceCoherentSource
    S hfineCutoff hcoarseCoupling source
  unfold wholeSlabRecouplingConditionalKernel
  exact divPos_eqv_congr_local
    (wholeSlabRecouplingPartition_pos coherent)
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source)
    (Q'.eqv_trans _ _ _
      (wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
        S source.1 targetState hfineCutoff source.2.1 htargetMem)
      (spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
        S (wholeSlabFinePacketTotalLabelling S source.1)
          targetState htargetMem))
    (wholeSlabRecouplingPartition_positivePhysicalSource_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling source)

/-- The literal production kernel row used in the observable and covariance
chains has the same normalized tilted-Gibbs formula for every positive fine
source. -/
theorem physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        source.1 targetState ≈
      Q'.divPos
        (Q'.ofNat
            (spinFourLoweringMultiplicityProduct S
              (wholeSlabFinePacketTotalLabelling S source.1)
              targetState) *
          S.coarse.physicalTerm targetState)
        (positivePhysicalSourceTiltedGibbsRowMass S source)
        (positivePhysicalSourceTiltedGibbsRowMass_pos
          S hfineCutoff hcoarseCoupling source) := by
  refine Q'.eqv_trans _
    (wholeSlabRecouplingConditionalKernel
      (positivePhysicalSourceCoherentSource
        S hfineCutoff hcoarseCoupling source) targetState) _ ?_ ?_
  · unfold physicalKernel SlabScalePair.FiniteSlabKernel.kernel
      cutoffOneWholeSlabFiniteKernel
      positivePhysicalSourceCoherentSource
    exact cutoffOneWholeSlabKernel_eq_positive
      S hfineCutoff hcoarseCoupling source.2.1 source.2.2 targetState
  · exact
      wholeSlabRecouplingConditionalKernel_positivePhysicalSource_eqv_tiltedGibbs
        S hfineCutoff hcoarseCoupling source targetState htargetMem

/-! ## 5. Axiom audit -/

#print axioms wholeSlabFinePacket_binary
#print axioms wholeSlabFinePacketTotalLabelling_le_four
#print axioms wholeSlabFaceRawWeight_eqv_totalLoweringFaceWeight
#print axioms wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
#print axioms wholeSlabRawRowMass_eqv_totalMultiplicityTiltedGibbs
#print axioms wholeSlabRecouplingPartition_positivePhysicalSource_eqv_tiltedGibbs
#print axioms positivePhysicalSourceTiltedGibbsRowMass_pos
#print axioms wholeSlabRecouplingConditionalKernel_positivePhysicalSource_eqv_tiltedGibbs
#print axioms physicalKernel_positivePhysicalSource_eqv_tiltedGibbs

end YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
