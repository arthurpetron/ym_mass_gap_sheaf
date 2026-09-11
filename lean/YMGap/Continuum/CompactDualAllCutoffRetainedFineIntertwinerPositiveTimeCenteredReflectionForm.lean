/-
# A strict centered reflected form on the enriched positive-time face

The three separate positive-time mismatch estimates need not be combined by
a lossy triangle inequality.  The centered reflected face form of the exact
enriched pushed law has the direct causal chain

  centered form <= joint event <= root event <= fine dyadic packet.

The last implication is proved row by row.  On a coherent row, positivity of
the coarse root is impossible when the fine packet is empty.  On an
incoherent positive row, the enriched kernel retains the fine state and the
selected fine root belongs to that packet.  Gibbs-null rows contribute zero.
Thus the named SU(2) anchor estimate gives the strict absolute bound
`256/425 < 1` while paying for the causal packet only once.

This is an exact centered covariance bound for one reflected Boolean
observable under the enriched finite pushed law.  Reflection covariance of
the observable and law has already been proved.  Positivity of this centered
form, a bound relative to its diagonal OS norm, a dense-vector operator gap,
scaling uniformity, and the continuum theorem remain open.

Constructive contract: finite normalized rational measures, exact kernel
Fubini, Boolean event support, and the existing SU(2) packet estimate only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, trusted external computation, heartbeat increase,
or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCanonicalDyadicGeometry

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCenteredReflectionForm

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCanonicalDyadicGeometry
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeSelectedFaceDyadicIncidence
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPushedReflection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact enriched reflected covariance -/

/-- Root-face moment under the exact enriched pushed law. -/
def enrichedLowerFaceBlockedMoment
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffRetainedBlockedExpectation S
    (enrichedLowerFaceObservable G)

/-- Reflected-face moment under the exact enriched pushed law. -/
def enrichedReflectedFaceBlockedMoment
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffRetainedBlockedExpectation S
    (enrichedReflectedFaceObservable G)

/-- Joint root/reflected-face moment under the exact enriched pushed law. -/
def enrichedLowerReflectedFaceBlockedMoment
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffRetainedBlockedExpectation S
    (enrichedLowerReflectedFaceObservable G)

/-- The centered reflected form of the one enriched face indicator.  The
joint observable is pointwise the product of the lower observable with its
reflected copy. -/
def enrichedPositiveTimeCenteredReflectionForm
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  enrichedLowerReflectedFaceBlockedMoment S G -
    enrichedLowerFaceBlockedMoment S G *
      enrichedReflectedFaceBlockedMoment S G

private theorem rationalBoolIndicator_nonnegative_local (value : Bool) :
    (0 : Q') ≤ rationalBoolIndicator value := by
  cases value <;> decide

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem allCutoffRetainedBlockedExpectation_nonnegative
    (S : SlabScalePair) (observable : AllCutoffRetainedTarget → Q')
    (hobservable : ∀ target, target ∈ allCutoffRetainedTargets S →
      (0 : Q') ≤ observable target) :
    (0 : Q') ≤ allCutoffRetainedBlockedExpectation S observable := by
  unfold allCutoffRetainedBlockedExpectation
  apply listQSum_nonnegative_on
  intro target htarget
  exact Q'.mul_nonneg _ _
    (allCutoffRetainedFineIntertwinerBlockedMass_nonnegative S target)
    (hobservable target htarget)

private theorem allCutoffRetainedBlockedExpectation_mono
    (S : SlabScalePair)
    (lower upper : AllCutoffRetainedTarget → Q')
    (hle : ∀ target, target ∈ allCutoffRetainedTargets S →
      lower target ≤ upper target) :
    allCutoffRetainedBlockedExpectation S lower ≤
      allCutoffRetainedBlockedExpectation S upper := by
  unfold allCutoffRetainedBlockedExpectation
  apply listQSum_mono
  intro target htarget
  apply Q'.mul_le_mul_of_nonneg_left
  · exact hle target htarget
  · exact allCutoffRetainedFineIntertwinerBlockedMass_nonnegative S target

private theorem enrichedLowerFaceObservable_nonnegative
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (target : AllCutoffRetainedTarget) :
    (0 : Q') ≤ enrichedLowerFaceObservable G target := by
  cases target <;> exact rationalBoolIndicator_nonnegative_local _

private theorem enrichedReflectedFaceObservable_nonnegative
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (target : AllCutoffRetainedTarget) :
    (0 : Q') ≤ enrichedReflectedFaceObservable G target := by
  cases target <;> exact rationalBoolIndicator_nonnegative_local _

private theorem rationalBoolIndicator_and_le_left
    (left right : Bool) :
    rationalBoolIndicator (left && right) ≤
      rationalBoolIndicator left := by
  cases left <;> cases right <;> decide

private theorem enrichedLowerReflectedFaceObservable_le_lower
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (target : AllCutoffRetainedTarget) :
    enrichedLowerReflectedFaceObservable G target ≤
      enrichedLowerFaceObservable G target := by
  cases target <;>
    exact rationalBoolIndicator_and_le_left _ _

theorem enrichedLowerReflectedFaceBlockedMoment_le_lower
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerReflectedFaceBlockedMoment S G ≤
      enrichedLowerFaceBlockedMoment S G := by
  unfold enrichedLowerReflectedFaceBlockedMoment
    enrichedLowerFaceBlockedMoment
  exact allCutoffRetainedBlockedExpectation_mono S _ _
    (fun target _ =>
      enrichedLowerReflectedFaceObservable_le_lower G target)

/-- Reflection invariance of the exact pushed law identifies the two
one-face moments. -/
theorem enrichedLowerFaceBlockedMoment_eqv_reflected
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (G : EnrichedLowerFaceGeometry S) :
    enrichedLowerFaceBlockedMoment S G ≈
      enrichedReflectedFaceBlockedMoment S G := by
  let lowerWeight : AllCutoffRetainedTarget → Q' :=
    fun target =>
      allCutoffRetainedFineIntertwinerBlockedMass S target *
        enrichedLowerFaceObservable G target
  let reflectedWeight : AllCutoffRetainedTarget → Q' :=
    fun target =>
      allCutoffRetainedFineIntertwinerBlockedMass S target *
        enrichedReflectedFaceObservable G target
  unfold enrichedLowerFaceBlockedMoment
    enrichedReflectedFaceBlockedMoment
    allCutoffRetainedBlockedExpectation
  change listQSum lowerWeight (allCutoffRetainedTargets S) ≈
    listQSum reflectedWeight (allCutoffRetainedTargets S)
  refine Q'.eqv_trans _
    (listQSum lowerWeight
      ((allCutoffRetainedTargets S).map
        (reflectAllCutoffRetainedTarget S))) _ ?_ ?_
  · exact listQSum_perm lowerWeight
      (allCutoffRetainedTargets_reflection_perm S).symm
  · rw [listQSum_map]
    apply listQSum_congr_on
    intro target htarget
    exact mul_eqv_both_local
      (allCutoffRetainedFineIntertwinerBlockedMass_reflection
        S hfineCutoff target htarget)
      (Q'.eqv_of_eq
        (enrichedLowerFaceObservable_reflection G target))

/-- The centered reflected form is therefore literally a same-object
connected moment: joint moment minus the square of the root mean. -/
theorem enrichedPositiveTimeCenteredReflectionForm_eqv_sameObject
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (G : EnrichedLowerFaceGeometry S) :
    enrichedPositiveTimeCenteredReflectionForm S G ≈
      enrichedLowerReflectedFaceBlockedMoment S G -
        enrichedLowerFaceBlockedMoment S G *
          enrichedLowerFaceBlockedMoment S G := by
  unfold enrichedPositiveTimeCenteredReflectionForm
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_refl _
  · apply Q'.neg_eqv_congr
    exact mul_eqv_both_local (Q'.eqv_refl _)
      (Q'.eqv_symm
        (enrichedLowerFaceBlockedMoment_eqv_reflected
          S hfineCutoff G))

/-- Centering can only decrease the upper bound because both one-face
moments are nonnegative. -/
theorem enrichedPositiveTimeCenteredReflectionForm_le_joint
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedPositiveTimeCenteredReflectionForm S G ≤
      enrichedLowerReflectedFaceBlockedMoment S G := by
  have hlower : (0 : Q') ≤ enrichedLowerFaceBlockedMoment S G := by
    unfold enrichedLowerFaceBlockedMoment
    exact allCutoffRetainedBlockedExpectation_nonnegative S _
      (fun target _ => enrichedLowerFaceObservable_nonnegative G target)
  have hreflected : (0 : Q') ≤
      enrichedReflectedFaceBlockedMoment S G := by
    unfold enrichedReflectedFaceBlockedMoment
    exact allCutoffRetainedBlockedExpectation_nonnegative S _
      (fun target _ => enrichedReflectedFaceObservable_nonnegative G target)
  have hproduct : (0 : Q') ≤
      enrichedLowerFaceBlockedMoment S G *
        enrichedReflectedFaceBlockedMoment S G :=
    Q'.mul_nonneg _ _ hlower hreflected
  have hneg :
      -(enrichedLowerFaceBlockedMoment S G *
        enrichedReflectedFaceBlockedMoment S G) ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg hproduct
  have hadd := Q'.add_le_add_left
    (enrichedLowerReflectedFaceBlockedMoment S G)
    (-(enrichedLowerFaceBlockedMoment S G *
      enrichedReflectedFaceBlockedMoment S G)) 0 hneg
  unfold enrichedPositiveTimeCenteredReflectionForm
  simpa only [Q'.add_zero'] using hadd

/-! ## 2. Rowwise causal support of the enriched root -/

private theorem coherentRecouplingEventMoment_le_one
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1)
    (coarseEvent : EdgeLabelling → Bool) :
    coherentRecouplingEventMoment S source hpartition coarseEvent ≤ 1 := by
  let coherent := coherentSlabRecouplingSourceOfRawPartitionPos
    S source.1 source.2 hpartition
  have hevent :
      finiteEventMass
          (wholeSlabRecouplingConditionalKernel coherent)
          S.coarse.physicalLabellings coarseEvent ≤ 1 :=
    finiteEventMass_le_one
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings coarseEvent
      (fun target _ =>
        wholeSlabRecouplingConditionalKernel_nonnegative coherent target)
      (wholeSlabRecouplingConditionalKernel_row_normalized coherent)
  refine Q'.le_trans' _
    (finiteEventMass
      (wholeSlabRecouplingConditionalKernel coherent)
      S.coarse.physicalLabellings coarseEvent) _ ?_ hevent
  unfold coherentRecouplingEventMoment finiteEventMass
  apply Q'.le_of_eqv
  apply listQSum_congr_on
  intro target _
  cases hevent : coarseEvent target
  · simp only [rationalBoolIndicator, Bool.false_eq_true, if_false]
    exact Q'.mul_zero_eqv _
  · simp only [rationalBoolIndicator, if_true]
    exact Q'.mul_one_eqv _

private theorem rationalBoolIndicator_le_of_true_imp
    (first second : Bool) (himp : first = true → second = true) :
    rationalBoolIndicator first ≤ rationalBoolIndicator second := by
  cases first <;> cases second
  · exact Q'.le_refl' 0
  · decide
  · simp at himp
  · exact Q'.le_refl' 1

private theorem coherentRootMoment_le_packetIndicator
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    coherentLowerFaceMoment G.base source hpartition ≤
      rationalBoolIndicator
        (dyadicFinePacketPositiveB
          S G.base.coarseRoot source.1) := by
  cases hpacket :
      dyadicFinePacketPositiveB S G.base.coarseRoot source.1
  · have hzero :=
      coherentRecouplingEventMoment_eqv_zero_of_emptyPacket_of_support
        S hfineCutoff source hpartition G.base.coarseRoot
        (by simpa only [SlabPhysicalData.faceEdges] using
          G.base.coarseRoot_mem)
        hpacket (slabPhysicalFacePositiveB G.base.coarseRoot)
        (fun _ hpositive => hpositive)
    unfold coherentLowerFaceMoment
    simp only [rationalBoolIndicator, Bool.false_eq_true, if_false]
    exact Q'.le_of_eqv hzero
  · simp only [rationalBoolIndicator, if_true]
    exact coherentRecouplingEventMoment_le_one S source hpartition
      (slabPhysicalFacePositiveB G.base.coarseRoot)

private theorem enrichedLowerFacePullback_le_packetIndicator_of_positive
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (G : DyadicEnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1) :
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G.base) source ≤
      rationalBoolIndicator
        (dyadicFinePacketPositiveB
          S G.base.coarseRoot source.1) := by
  by_cases hpartition :
      (0 : Q') < wholeSlabRawRowPartition S source.1
  · exact Q'.le_trans' _
      (coherentLowerFaceMoment G.base source hpartition) _
      (Q'.le_of_eqv
        (enrichedLowerFacePullback_eqv_coherentMoment
          G.base source hpositive hpartition))
      (coherentRootMoment_le_packetIndicator
        S hfineCutoff G source hpartition)
  · have hpullback :=
      enrichedLowerFacePullback_eqv_fineIndicator_of_incoherent
        G.base source hpositive hpartition
    refine Q'.le_trans' _
      (rationalBoolIndicator
        (slabPhysicalFacePositiveB G.base.fineRoot source.1)) _
      (Q'.le_of_eqv hpullback) ?_
    apply rationalBoolIndicator_le_of_true_imp
    intro hfinePositive
    exact selectedFineFacePositive_implies_packetPositive
      S source.1 G.base.fineRoot G.base.coarseRoot
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem)
      G.fineRoot_mem_packet hfinePositive

/-! ## 3. Average support and the strict anchor endpoint -/

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

/-- The enriched root occupation is bounded by the complete normalized
fine-law occupation of its causal dyadic packet. -/
theorem enrichedLowerFaceBlockedMoment_le_packetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (G : DyadicEnrichedLowerFaceGeometry S) :
    enrichedLowerFaceBlockedMoment S G.base ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S G.base.coarseRoot) := by
  let packet := dyadicFinePacketPositiveB S G.base.coarseRoot
  have hsource :
      allCutoffFinePhysicalExpectation S
          (allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G.base)) ≤
        allCutoffFinePhysicalExpectation S
          (fun source => rationalBoolIndicator (packet source.1)) := by
    unfold allCutoffFinePhysicalExpectation
    apply listQSum_mono
    intro source _
    by_cases hpositive :
        (0 : Q') < S.fine.physicalTerm source.1
    · apply Q'.mul_le_mul_of_nonneg_left
      · exact enrichedLowerFacePullback_le_packetIndicator_of_positive
          S hfineCutoff G source hpositive
      · exact S.fine.normalizedMass_nonnegative source.1
    · have hmassZero := normalizedMass_eqv_zero_of_not_positive
        S.fine source.1 hpositive
      have hleftZero :
          S.fine.normalizedMass source.1 *
              allCutoffRetainedObservablePullback S
                (enrichedLowerFaceObservable G.base) source ≈ 0 :=
        Q'.eqv_trans _
          (0 * allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G.base) source) _
          (Q'.mul_eqv_congr_right _ _ _ hmassZero)
          (Q'.zero_mul_eqv _)
      exact Q'.le_trans' _ 0 _
        (Q'.le_of_eqv hleftZero)
        (Q'.mul_nonneg _ _
          (S.fine.normalizedMass_nonnegative source.1)
          (rationalBoolIndicator_nonnegative_local (packet source.1)))
  refine Q'.le_trans' _
    (allCutoffFinePhysicalExpectation S
      (allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G.base))) _ ?_ ?_
  · unfold enrichedLowerFaceBlockedMoment
    exact Q'.le_of_eqv
      (allCutoffRetainedBlockedExpectation_eqv_pullback
        S (enrichedLowerFaceObservable G.base))
  · exact Q'.le_trans' _
      (allCutoffFinePhysicalExpectation S
        (fun source => rationalBoolIndicator (packet source.1))) _
      hsource
      (Q'.le_of_eqv
        (fineIndicatorExpectation_eqv_normalizedEventMass S packet))

/-- The complete causal chain for the centered reflected form. -/
theorem enrichedPositiveTimeCenteredReflectionForm_le_packetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (G : DyadicEnrichedLowerFaceGeometry S) :
    enrichedPositiveTimeCenteredReflectionForm S G.base ≤
      normalizedSlabEventMass S.fine
        (dyadicFinePacketPositiveB S G.base.coarseRoot) := by
  exact Q'.le_trans' _
    (enrichedLowerReflectedFaceBlockedMoment S G.base) _
    (enrichedPositiveTimeCenteredReflectionForm_le_joint S G.base)
    (Q'.le_trans' _
      (enrichedLowerFaceBlockedMoment S G.base) _
      (enrichedLowerReflectedFaceBlockedMoment_le_lower S G.base)
      (enrichedLowerFaceBlockedMoment_le_packetMass
        S hfineCutoff G))

/-- **Strict canonical centered reflected-form bound.**  At fine cutoff one
and the explicitly named SU(2) anchor, the exact enriched centered reflected
face covariance is at most `256/425`.  The cutoff and finite volume remain
named; no scaling or operator-norm uniformity is claimed. -/
theorem canonicalBottomEnrichedPositiveTimeCenteredReflectionForm_le_twoFiftySixFourTwentyFive
    (S : SlabScalePair) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedPositiveTimeCenteredReflectionForm S
        (canonicalBottomDyadicEnrichedLowerFaceGeometry S).base ≤
      Q'.mkPos 256 425 (by decide) := by
  let G := canonicalBottomDyadicEnrichedLowerFaceGeometry S
  exact Q'.le_trans' _
    (normalizedSlabEventMass S.fine
      (dyadicFinePacketPositiveB S G.base.coarseRoot)) _
    (enrichedPositiveTimeCenteredReflectionForm_le_packetMass
      S hfineCutoff G)
    (normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
      S cutoff half G.base.coarseRoot hfine
      (by simpa only [SlabPhysicalData.faceEdges] using
        G.base.coarseRoot_mem))

theorem canonicalBottomEnrichedPositiveTimeCenteredReflectionForm_lt_one
    (S : SlabScalePair) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hfineCutoff : S.fine.cutoff = 1) :
    enrichedPositiveTimeCenteredReflectionForm S
        (canonicalBottomDyadicEnrichedLowerFaceGeometry S).base < 1 := by
  exact Q'.lt_of_le_of_lt
    (canonicalBottomEnrichedPositiveTimeCenteredReflectionForm_le_twoFiftySixFourTwentyFive
      S cutoff half hfine hfineCutoff)
    twoFiftySixFourTwentyFive_lt_one

#print axioms enrichedPositiveTimeCenteredReflectionForm
#print axioms enrichedLowerReflectedFaceBlockedMoment_le_lower
#print axioms enrichedLowerFaceBlockedMoment_eqv_reflected
#print axioms enrichedPositiveTimeCenteredReflectionForm_eqv_sameObject
#print axioms enrichedPositiveTimeCenteredReflectionForm_le_joint
#print axioms enrichedLowerFaceBlockedMoment_le_packetMass
#print axioms enrichedPositiveTimeCenteredReflectionForm_le_packetMass
#print axioms canonicalBottomEnrichedPositiveTimeCenteredReflectionForm_le_twoFiftySixFourTwentyFive
#print axioms canonicalBottomEnrichedPositiveTimeCenteredReflectionForm_lt_one

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCenteredReflectionForm
