/-
# Support-swap response in exact tilted-Gibbs coordinates

The target-rooted fine-source support swap leaves one analytic response
defect in the occupation-cocycle decomposition.  The all-source lowering
theorem identifies each of its four positive production rows with an
explicit integer-tilted coarse Gibbs law.  This file performs that
substitution and records the exact locality criterion which kills the
defect: the two rows on each side need only retain the same facewise packet
total profile.

This is a bridge to a connected perturbation estimate, not that estimate.
In particular, no total-variation bound, volume-uniform centered-remainder
bound, continuum construction, OS/GNS reconstruction, Hamiltonian gap, or
Yang--Mills mass gap is asserted here.

Constructive contract: exact finite sums and rational equivalence only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSignedAverage
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSignedAverage
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem sub_eqv_zero_of_eqv_local {a b : Q'}
    (h : a ≈ b) : a - b ≈ 0 := by
  exact Q'.eqv_trans _ (b + -b) _
    (Q'.add_eqv_congr' h (Q'.eqv_refl _))
    (Q'.add_neg_self_eqv b)

private theorem divPos_eqv_congr_local
    {numerator numerator' denominator denominator' : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominator' : (0 : Q') < denominator')
    (hnumerator : numerator ≈ numerator')
    (hdenominatorEq : denominator ≈ denominator') :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator' denominator' hdenominator' := by
  apply Q'.eqv_of_le_le
  · apply Q'.le_divPos_of_mul_le numerator' denominator' hdenominator'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator hdenominator)
          denominator' denominator (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le numerator denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator' hdenominator')
          denominator denominator' hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv numerator' denominator' hdenominator')
          (Q'.eqv_symm hnumerator)))

/-! ## 1. Event masses of the explicit tilted rows -/

/-- Boolean event mass under one source-dependent integer-tilted coarse
Gibbs row. -/
def positivePhysicalSourceTiltedGibbsEventMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) : Q' :=
  finiteEventMass
    (positivePhysicalSourceTiltedGibbsKernel
      S hfineCutoff hcoarseCoupling source)
    S.coarse.physicalLabellings event

/-- Every positive production-row event response is exactly the event mass
of its explicit tilted-Gibbs law. -/
theorem fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling) source.1 event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling source event := by
  refine Q'.eqv_trans _
    (finiteEventMass
      ((physicalKernel S hfineCutoff hcoarseCoupling).kernel source.1)
      S.coarse.physicalLabellings event) _ ?_ ?_
  · unfold fineCouplingKernelOutputEventMass finiteEventMass
    exact listQSum_filter
      ((physicalKernel S hfineCutoff hcoarseCoupling).kernel source.1)
      event S.coarse.physicalLabellings
  · unfold positivePhysicalSourceTiltedGibbsEventMass finiteEventMass
    apply listQSum_congr_on
    intro targetState htargetMem
    cases hevent : event targetState with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact Q'.eqv_refl 0
    | true =>
        simp only [if_true]
        exact physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
          S hfineCutoff hcoarseCoupling source targetState htargetMem

/-! ## 2. The row law depends only on the packet-total profile -/

/-- Two fine sources have the same production-row profile when their
four-bit packet totals agree on every physical coarse face.  No equality is
required away from the finite carrier read by the kernel. -/
def finePacketTotalProfilesAgreeOnCoarseFaces
    (S : SlabScalePair) (first second : EdgeLabelling) : Prop :=
  ∀ faceId, faceId ∈ S.coarse.faceEdges →
    wholeSlabFinePacketTotalLabelling S first faceId =
      wholeSlabFinePacketTotalLabelling S second faceId

/-- Literal finite support on which two fine sources induce different
coarse packet totals. -/
def finePacketTotalDisagreementCoarseFaces
    (S : SlabScalePair) (first second : EdgeLabelling) : List Nat :=
  S.coarse.faceEdges.filter fun faceId =>
    decide
      (wholeSlabFinePacketTotalLabelling S first faceId ≠
        wholeSlabFinePacketTotalLabelling S second faceId)

private theorem filter_eq_nil_of_all_false_local {A : Type}
    (test : A → Bool) : ∀ items : List A,
    (∀ item, item ∈ items → test item = false) →
      items.filter test = []
  | [], _ => rfl
  | head :: tail, hfalse => by
      have hhead := hfalse head List.mem_cons_self
      have htail := filter_eq_nil_of_all_false_local test tail
        (fun item hmem =>
          hfalse item (List.mem_cons_of_mem head hmem))
      simp [hhead, htail]

/-- The disagreement carrier is empty exactly when the two source profiles
agree on every physical coarse face. -/
theorem finePacketTotalDisagreementCoarseFaces_eq_nil_iff
    (S : SlabScalePair) (first second : EdgeLabelling) :
    finePacketTotalDisagreementCoarseFaces S first second = [] ↔
      finePacketTotalProfilesAgreeOnCoarseFaces S first second := by
  constructor
  · intro hempty faceId hface
    by_cases heq : wholeSlabFinePacketTotalLabelling S first faceId =
        wholeSlabFinePacketTotalLabelling S second faceId
    · exact heq
    · have hmem : faceId ∈
          finePacketTotalDisagreementCoarseFaces S first second := by
        unfold finePacketTotalDisagreementCoarseFaces
        exact List.mem_filter.mpr ⟨hface, decide_eq_true heq⟩
      rw [hempty] at hmem
      exact False.elim (List.not_mem_nil hmem)
  · intro hagree
    unfold finePacketTotalDisagreementCoarseFaces
    apply filter_eq_nil_of_all_false_local
    intro faceId hface
    simp only [hagree faceId hface, ne_eq, not_true, decide_false]

private theorem bool_eq_of_true_iff_true_local
    (left right : Bool) (h : left = true ↔ right = true) :
    left = right := by
  cases left <;> cases right <;> simp_all

/-- Pointwise lowering tests are identical for source profiles which agree
on the finite coarse-face carrier. -/
theorem spinFourPointwiseLoweringB_eq_of_packetTotalsAgree
    (S : SlabScalePair) (first second targetState : EdgeLabelling)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first second) :
    spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S first) targetState =
      spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S second) targetState := by
  apply bool_eq_of_true_iff_true_local
  rw [spinFourPointwiseLoweringB_true_iff,
    spinFourPointwiseLoweringB_true_iff]
  constructor
  · intro hfirst faceId hface
    rw [← hprofile faceId hface]
    exact hfirst faceId hface
  · intro hsecond faceId hface
    rw [hprofile faceId hface]
    exact hsecond faceId hface

/-- The exact lowering carriers are identical when the finite packet-total
profiles agree. -/
theorem spinFourLoweringTargets_eq_of_packetTotalsAgree
    (S : SlabScalePair) (first second : EdgeLabelling)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first second) :
    spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S first) =
      spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S second) := by
  unfold spinFourLoweringTargets
  have htest :
      spinFourPointwiseLoweringB S
          (wholeSlabFinePacketTotalLabelling S first) =
        spinFourPointwiseLoweringB S
          (wholeSlabFinePacketTotalLabelling S second) := by
    funext targetState
    exact spinFourPointwiseLoweringB_eq_of_packetTotalsAgree
      S first second targetState hprofile
  rw [htest]

/-- The all-face fusion-path multiplier reads the source profile only on the
physical coarse-face carrier. -/
theorem spinFourLoweringMultiplicityProduct_eq_of_packetTotalsAgree
    (S : SlabScalePair) (first second targetState : EdgeLabelling)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first second) :
    spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S first) targetState =
      spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S second) targetState := by
  unfold spinFourLoweringMultiplicityProduct
  apply natListProduct_congr
  intro faceId hface
  rw [hprofile faceId hface]

/-- The tilted denominator depends only on packet totals on the finite
physical coarse-face carrier. -/
theorem positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotalsAgree
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first.1 second.1) :
    positivePhysicalSourceTiltedGibbsRowMass S first =
      positivePhysicalSourceTiltedGibbsRowMass S second := by
  unfold positivePhysicalSourceTiltedGibbsRowMass
  rw [spinFourLoweringTargets_eq_of_packetTotalsAgree
    S first.1 second.1 hprofile]
  have hweight :
      (fun targetState =>
        Q'.ofNat
            (spinFourLoweringMultiplicityProduct S
              (wholeSlabFinePacketTotalLabelling S first.1)
              targetState) *
          S.coarse.physicalTerm targetState) =
        (fun targetState =>
          Q'.ofNat
              (spinFourLoweringMultiplicityProduct S
                (wholeSlabFinePacketTotalLabelling S second.1)
                targetState) *
            S.coarse.physicalTerm targetState) := by
    funext targetState
    rw [spinFourLoweringMultiplicityProduct_eq_of_packetTotalsAgree
      S first.1 second.1 targetState hprofile]
  rw [hweight]

/-- The tilted denominator depends on a positive fine source only through
its facewise four-bit packet-total labelling. -/
theorem positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotal_eq
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (hprofile : wholeSlabFinePacketTotalLabelling S first.1 =
      wholeSlabFinePacketTotalLabelling S second.1) :
    positivePhysicalSourceTiltedGibbsRowMass S first =
      positivePhysicalSourceTiltedGibbsRowMass S second := by
  apply positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotalsAgree
  intro faceId _hface
  exact congrFun hprofile faceId

/-- Finite-carrier profile agreement gives pointwise equivalent normalized
tilted rows. -/
theorem positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotalsAgree
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first.1 second.1)
    (targetState : EdgeLabelling) :
    positivePhysicalSourceTiltedGibbsKernel
        S hfineCutoff hcoarseCoupling first targetState ≈
      positivePhysicalSourceTiltedGibbsKernel
        S hfineCutoff hcoarseCoupling second targetState := by
  unfold positivePhysicalSourceTiltedGibbsKernel
  apply divPos_eqv_congr_local
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling first)
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling second)
  · apply Q'.eqv_of_eq
    rw [spinFourLoweringMultiplicityProduct_eq_of_packetTotalsAgree
      S first.1 second.1 targetState hprofile]
  · exact Q'.eqv_of_eq
      (positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotalsAgree
        S first second hprofile)

/-- Equal packet-total profiles give pointwise equivalent normalized tilted
rows.  Positivity proofs do not enter the numerical law. -/
theorem positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotal_eq
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (hprofile : wholeSlabFinePacketTotalLabelling S first.1 =
      wholeSlabFinePacketTotalLabelling S second.1)
    (targetState : EdgeLabelling) :
    positivePhysicalSourceTiltedGibbsKernel
        S hfineCutoff hcoarseCoupling first targetState ≈
      positivePhysicalSourceTiltedGibbsKernel
        S hfineCutoff hcoarseCoupling second targetState := by
  apply positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotalsAgree
  intro faceId _hface
  exact congrFun hprofile faceId

/-- Finite-carrier packet-total agreement identifies every Boolean event
mass of the two tilted rows. -/
theorem positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotalsAgree
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (hprofile : finePacketTotalProfilesAgreeOnCoarseFaces
      S first.1 second.1)
    (event : EdgeLabelling → Bool) :
    positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling first event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling second event := by
  unfold positivePhysicalSourceTiltedGibbsEventMass finiteEventMass
  apply listQSum_congr_on
  intro targetState _htargetMem
  cases hevent : event targetState with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
  | true =>
      simp only [if_true]
      exact positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotalsAgree
        S hfineCutoff hcoarseCoupling first second hprofile targetState

/-- The same packet-total criterion identifies every Boolean event mass. -/
theorem positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotal_eq
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (hprofile : wholeSlabFinePacketTotalLabelling S first.1 =
      wholeSlabFinePacketTotalLabelling S second.1)
    (event : EdgeLabelling → Bool) :
    positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling first event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling second event := by
  apply positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotalsAgree
  intro faceId _hface
  exact congrFun hprofile faceId

/-! ## 3. Accepted support-swap rows in tilted coordinates -/

/-- The accepted left source, with its existing strict positivity witness. -/
def fineCouplingAcceptedSeparatedLeftPositiveSource
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : PositivePhysicalSource S :=
  ⟨(fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source).1,
    source.1.1.physical_mem,
    fineCouplingAcceptedSeparated_left_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId source⟩

/-- The accepted right source, with its existing strict positivity witness. -/
def fineCouplingAcceptedSeparatedRightPositiveSource
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : PositivePhysicalSource S :=
  ⟨(fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source).2,
    (mem_slabExpandedFineSources_iff.mp source.1.2.2).1,
    fineCouplingAcceptedSeparated_right_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId source⟩

/-- The support-swapped left source, with the assignment-produced strict
positivity witness. -/
def fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : PositivePhysicalSource S :=
  ⟨slabObservablePairSupportSwitchedLeftPhysical
      S.fine targetFaceId source.1,
    slabObservablePairedSupportSwitchedLeftPhysical_mem S.fine source,
    fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId htarget source⟩

/-- The support-swapped right source, with the assignment-produced strict
positivity witness. -/
def fineCouplingAcceptedSeparatedSwappedRightPositiveSource
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : PositivePhysicalSource S :=
  ⟨slabObservablePairSupportSwitchedRightPhysical
      S.fine targetFaceId source.1,
    slabObservablePairedSupportSwitchedRightPhysical_mem S.fine source,
    fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId htarget source⟩

theorem fineCouplingAcceptedSeparatedLeft_eventMass_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).1 event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling
          (fineCouplingAcceptedSeparatedLeftPositiveSource
            S hfineCoupling rootFaceId targetFaceId source) event := by
  simpa only [fineCouplingAcceptedSeparatedLeftPositiveSource] using
    (fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling
        (fineCouplingAcceptedSeparatedLeftPositiveSource
          S hfineCoupling rootFaceId targetFaceId source) event)

theorem fineCouplingAcceptedSeparatedRight_eventMass_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).2 event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling
          (fineCouplingAcceptedSeparatedRightPositiveSource
            S hfineCoupling rootFaceId targetFaceId source) event := by
  simpa only [fineCouplingAcceptedSeparatedRightPositiveSource] using
    (fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling
        (fineCouplingAcceptedSeparatedRightPositiveSource
          S hfineCoupling rootFaceId targetFaceId source) event)

theorem fineCouplingAcceptedSeparatedSwappedLeft_eventMass_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        (slabObservablePairSupportSwitchedLeftPhysical
          S.fine targetFaceId source.1) event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling
          (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
            S hfineCoupling rootFaceId targetFaceId htarget source) event := by
  simpa only [fineCouplingAcceptedSeparatedSwappedLeftPositiveSource] using
    (fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling
        (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
          S hfineCoupling rootFaceId targetFaceId htarget source) event)

theorem fineCouplingAcceptedSeparatedSwappedRight_eventMass_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling)
        (slabObservablePairSupportSwitchedRightPhysical
          S.fine targetFaceId source.1) event ≈
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling
          (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
            S hfineCoupling rootFaceId targetFaceId htarget source) event := by
  simpa only [fineCouplingAcceptedSeparatedSwappedRightPositiveSource] using
    (fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
      S hfineCutoff hcoarseCoupling
        (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
          S hfineCoupling rootFaceId targetFaceId htarget source) event)

/-- The actual support-swap response defect is a signed four-row contrast
of explicit integer-tilted coarse Gibbs event masses. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let left := fineCouplingAcceptedSeparatedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId source
    let right := fineCouplingAcceptedSeparatedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId source
    let swappedLeft := fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source
    let swappedRight := fineCouplingAcceptedSeparatedSwappedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event targetFaceId pair ≈
      (positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling left event -
        positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling right event) -
      (positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling swappedLeft event -
        positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling swappedRight event) := by
  dsimp only
  unfold fineCouplingPhysicalSupportSwapResponseDefect
    fineCouplingPhysicalPairEventResponseDifference
  rw [fineCouplingAcceptedSeparated_supportSwapped_left
      S rootFaceId targetFaceId source,
    fineCouplingAcceptedSeparated_supportSwapped_right
      S rootFaceId targetFaceId source]
  apply sub_eqv_both_local
  · exact sub_eqv_both_local
      (fineCouplingAcceptedSeparatedLeft_eventMass_eqv_tiltedGibbs
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId source event)
      (fineCouplingAcceptedSeparatedRight_eventMass_eqv_tiltedGibbs
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId source event)
  · exact sub_eqv_both_local
      (fineCouplingAcceptedSeparatedSwappedLeft_eventMass_eqv_tiltedGibbs
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event)
      (fineCouplingAcceptedSeparatedSwappedRight_eventMass_eqv_tiltedGibbs
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event)

/-- If the target-rooted support swap changes neither row's packet-total
profile, the production-kernel response defect vanishes exactly.  This
isolates the future connected estimate to swaps with nonempty coarse packet
support. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_packetTotals
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool)
    (hleft : finePacketTotalProfilesAgreeOnCoarseFaces S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1)
    (hright : finePacketTotalProfilesAgreeOnCoarseFaces S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1) :
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) ≈ 0 := by
  let left := fineCouplingAcceptedSeparatedLeftPositiveSource
    S hfineCoupling rootFaceId targetFaceId source
  let right := fineCouplingAcceptedSeparatedRightPositiveSource
    S hfineCoupling rootFaceId targetFaceId source
  let swappedLeft := fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
    S hfineCoupling rootFaceId targetFaceId htarget source
  let swappedRight := fineCouplingAcceptedSeparatedSwappedRightPositiveSource
    S hfineCoupling rootFaceId targetFaceId htarget source
  have hleftMass :
      positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling left event ≈
        positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling swappedLeft event :=
    positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotalsAgree
      S hfineCutoff hcoarseCoupling left swappedLeft hleft event
  have hrightMass :
      positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling right event ≈
        positivePhysicalSourceTiltedGibbsEventMass
          S hfineCutoff hcoarseCoupling swappedRight event :=
    positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotalsAgree
      S hfineCutoff hcoarseCoupling right swappedRight hright event
  have hcontrast :
      positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling left event -
          positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling right event ≈
        positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling swappedLeft event -
          positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling swappedRight event :=
    sub_eqv_both_local hleftMass hrightMass
  exact Q'.eqv_trans _ _ _
    (fineCouplingAcceptedSeparated_actualResponseDefect_eqv_tiltedGibbs
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source event)
    (sub_eqv_zero_of_eqv_local hcontrast)

/-- Coarse faces on which the accepted left row's packet-total profile is
changed by the target-rooted support swap. -/
def fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : List Nat :=
  finePacketTotalDisagreementCoarseFaces S
    (fineCouplingAcceptedSeparatedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
    (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1

/-- Coarse faces on which the accepted right row's packet-total profile is
changed by the same support swap. -/
def fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : List Nat :=
  finePacketTotalDisagreementCoarseFaces S
    (fineCouplingAcceptedSeparatedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
    (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1

/-- Empty packet-total disagreement support in both replicas makes the
actual production response defect vanish.  Hence every surviving defect has
a literal nonempty finite coarse-face carrier to which a connected estimate
can attach. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_disagreementFaces_nil
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool)
    (hleft :
      fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source = [])
    (hright :
      fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source = []) :
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) ≈ 0 := by
  apply
    fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_packetTotals
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source event
  · exact (finePacketTotalDisagreementCoarseFaces_eq_nil_iff S _ _).mp
      (by simpa only
        [fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces]
        using hleft)
  · exact (finePacketTotalDisagreementCoarseFaces_eq_nil_iff S _ _).mp
      (by simpa only
        [fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces]
        using hright)

/-! ## 4. Axiom audit -/

#print axioms positivePhysicalSourceTiltedGibbsEventMass
#print axioms fineCouplingPhysicalKernelOutputEventMass_eqv_tiltedGibbs
#print axioms finePacketTotalDisagreementCoarseFaces_eq_nil_iff
#print axioms spinFourLoweringTargets_eq_of_packetTotalsAgree
#print axioms spinFourLoweringMultiplicityProduct_eq_of_packetTotalsAgree
#print axioms positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotalsAgree
#print axioms positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotalsAgree
#print axioms positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotalsAgree
#print axioms positivePhysicalSourceTiltedGibbsRowMass_eq_of_packetTotal_eq
#print axioms positivePhysicalSourceTiltedGibbsKernel_eqv_of_packetTotal_eq
#print axioms positivePhysicalSourceTiltedGibbsEventMass_eqv_of_packetTotal_eq
#print axioms fineCouplingAcceptedSeparatedLeftPositiveSource
#print axioms fineCouplingAcceptedSeparatedRightPositiveSource
#print axioms fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
#print axioms fineCouplingAcceptedSeparatedSwappedRightPositiveSource
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_tiltedGibbs
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_packetTotals
#print axioms fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
#print axioms fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_disagreementFaces_nil

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
