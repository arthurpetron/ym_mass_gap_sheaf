/-
# Total covariance for the enriched positive-time block map

The centered reflected form of the enriched pushed law has two mathematically
distinct sources.  The law of total covariance separates them exactly:

  target centered form
    = centered form of the two source-side pullbacks
      + source average of the covariance created inside one kernel row.

For the retained fine-intertwiner kernel, every positive incoherent row keeps
the physical state fixed.  Its root, reflected, and joint face moments are
therefore deterministic and its conditional covariance is exactly zero.
Rows with nonpositive Gibbs weight disappear after multiplication by their
normalized source mass.  Consequently the entire conditional correction is
supported on positive coherent recoupling rows.

This is the exact probabilistic decomposition needed before attempting
reflection positivity.  It does not assert that either summand is
nonnegative: source-side positivity still requires positive-time locality of
the pullback, and coherent-row positivity still requires an actual
half-space factorization of the recoupling row.  No spectral, scaling, or
continuum conclusion is claimed.

Constructive contract: finite sums and exact rational algebra only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, trusted external computation, or heartbeat
increase.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCenteredReflectionForm

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeTotalCovariance

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerObservablePullback
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeCenteredReflectionForm
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeFaceCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeMomentCompiler
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_neg_local right items)

private theorem weighted_sub_eqv (weight left right : Q') :
    weight * (left - right) ≈
      weight * left - weight * right := by
  change weight * (left + -right) ≈
    weight * left + -(weight * right)
  ring_qeqv

private theorem add_sub_left_cancel_eqv (base extra : Q') :
    (base + extra) + -base ≈ extra := by
  refine Q'.eqv_trans _ (base + (extra + -base)) _
    (Q'.add_assoc_eqv base extra (-base)) ?_
  refine Q'.eqv_trans _ (base + (-base + extra)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl base)
      (Q'.add_comm_eqv extra (-base))) ?_
  refine Q'.eqv_trans _ ((base + -base) + extra) _
    (Q'.eqv_symm (Q'.add_assoc_eqv base (-base) extra)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + extra) _
    (Q'.add_eqv_congr' (Q'.add_neg_self_eqv base)
      (Q'.eqv_refl extra)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' extra)

private theorem covariance_telescope_eqv
    (product centered joint : Q') :
    (product - centered) + (joint - product) ≈
      joint - centered := by
  change (product + -centered) + (joint + -product) ≈
    joint + -centered
  refine Q'.eqv_trans _
    (((product + -centered) + joint) + -product) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (product + -centered) joint (-product))) ?_
  refine Q'.eqv_trans _
    ((product + (joint + -centered)) + -product) _ ?_ ?_
  · apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (product + (-centered + joint)) _
        (Q'.add_assoc_eqv product (-centered) joint) ?_
      exact Q'.add_eqv_congr' (Q'.eqv_refl product)
        (Q'.add_comm_eqv (-centered) joint)
    · exact Q'.eqv_refl _
  · exact add_sub_left_cancel_eqv product (joint + -centered)

private theorem allCutoffFinePhysicalExpectation_sub
    (S : SlabScalePair)
    (left right : SlabPhysicalSourceEntry S.fine → Q') :
    allCutoffFinePhysicalExpectation S
        (fun source => left source - right source) ≈
      allCutoffFinePhysicalExpectation S left -
        allCutoffFinePhysicalExpectation S right := by
  unfold allCutoffFinePhysicalExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        S.fine.normalizedMass source.1 * left source -
          S.fine.normalizedMass source.1 * right source)
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    exact weighted_sub_eqv
      (S.fine.normalizedMass source.1) (left source) (right source)
  · exact listQSum_sub_local _ _ _

/-! ## 1. The two summands -/

/-- Covariance of the root and reflected observables inside one enriched
kernel row. -/
def enrichedPositiveTimeRowReflectionCovariance
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine) : Q' :=
  allCutoffRetainedObservablePullback S
      (enrichedLowerReflectedFaceObservable G) source -
    allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G) source *
      allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source

/-- Source average of the conditional row covariance. -/
def enrichedPositiveTimeAverageRowReflectionCovariance
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffFinePhysicalExpectation S
    (enrichedPositiveTimeRowReflectionCovariance S G)

/-- Centered reflected form of the two conditional expectations on the fine
source carrier.  This is the first term in the law of total covariance. -/
def enrichedPositiveTimePulledCenteredReflectionForm
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffFinePhysicalExpectation S
      (fun source =>
        allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G) source *
          allCutoffRetainedObservablePullback S
            (enrichedReflectedFaceObservable G) source) -
    allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S
          (enrichedLowerFaceObservable G)) *
      allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S
          (enrichedReflectedFaceObservable G))

/-- The same source-side form written with one pullback and its reflected
source value. -/
def enrichedPositiveTimePulledSameObjectReflectionForm
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  allCutoffFinePhysicalExpectation S
      (fun source =>
        allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G) source *
          allCutoffRetainedObservablePullback S
            (enrichedLowerFaceObservable G)
            (reflectSlabPhysicalSourceEntry source)) -
    allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S
          (enrichedLowerFaceObservable G)) *
      allCutoffFinePhysicalExpectation S
        (allCutoffRetainedObservablePullback S
          (enrichedLowerFaceObservable G))

/-- Reflection intertwining turns the pulled term into a literal same-object
source reflection form.  Whether its pullback is positive-time local is a
separate geometric question. -/
theorem enrichedPositiveTimePulledCenteredReflectionForm_eqv_sameObject
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (G : EnrichedLowerFaceGeometry S) :
    enrichedPositiveTimePulledCenteredReflectionForm S G ≈
      enrichedPositiveTimePulledSameObjectReflectionForm S G := by
  let lowerPullback := allCutoffRetainedObservablePullback S
    (enrichedLowerFaceObservable G)
  let reflectedPullback := allCutoffRetainedObservablePullback S
    (enrichedReflectedFaceObservable G)
  have hproduct :
      allCutoffFinePhysicalExpectation S
          (fun source => lowerPullback source * reflectedPullback source) ≈
        allCutoffFinePhysicalExpectation S
          (fun source =>
            lowerPullback source *
              lowerPullback (reflectSlabPhysicalSourceEntry source)) := by
    unfold allCutoffFinePhysicalExpectation
    apply listQSum_congr_on
    intro source _
    apply Q'.mul_eqv_congr_left
    exact mul_eqv_both_local (Q'.eqv_refl _)
      (Q'.eqv_symm
        (enrichedLowerFacePullback_reflection
          hfineCutoff G source))
  have hmean :
      allCutoffFinePhysicalExpectation S reflectedPullback ≈
        allCutoffFinePhysicalExpectation S lowerPullback := by
    refine Q'.eqv_trans _
      (enrichedReflectedFaceBlockedMoment S G) _ ?_ ?_
    · exact Q'.eqv_symm
        (allCutoffRetainedBlockedExpectation_eqv_pullback
          S (enrichedReflectedFaceObservable G))
    refine Q'.eqv_trans _
      (enrichedLowerFaceBlockedMoment S G) _ ?_ ?_
    · exact Q'.eqv_symm
        (enrichedLowerFaceBlockedMoment_eqv_reflected
          S hfineCutoff G)
    · exact allCutoffRetainedBlockedExpectation_eqv_pullback
        S (enrichedLowerFaceObservable G)
  unfold enrichedPositiveTimePulledCenteredReflectionForm
    enrichedPositiveTimePulledSameObjectReflectionForm
  exact Q'.add_eqv_congr' hproduct
    (Q'.neg_eqv_congr _ _
      (mul_eqv_both_local (Q'.eqv_refl _) hmean))

/-- Exact law of total covariance for the enriched reflected face. -/
theorem enrichedPositiveTimeCenteredReflectionForm_eqv_pulled_add_row
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedPositiveTimeCenteredReflectionForm S G ≈
      enrichedPositiveTimePulledCenteredReflectionForm S G +
        enrichedPositiveTimeAverageRowReflectionCovariance S G := by
  let lowerPullback := allCutoffRetainedObservablePullback S
    (enrichedLowerFaceObservable G)
  let reflectedPullback := allCutoffRetainedObservablePullback S
    (enrichedReflectedFaceObservable G)
  let jointPullback := allCutoffRetainedObservablePullback S
    (enrichedLowerReflectedFaceObservable G)
  let pullbackProduct := fun source =>
    lowerPullback source * reflectedPullback source
  have hjoint : enrichedLowerReflectedFaceBlockedMoment S G ≈
      allCutoffFinePhysicalExpectation S jointPullback := by
    unfold enrichedLowerReflectedFaceBlockedMoment jointPullback
    exact allCutoffRetainedBlockedExpectation_eqv_pullback
      S (enrichedLowerReflectedFaceObservable G)
  have hlower : enrichedLowerFaceBlockedMoment S G ≈
      allCutoffFinePhysicalExpectation S lowerPullback := by
    unfold enrichedLowerFaceBlockedMoment lowerPullback
    exact allCutoffRetainedBlockedExpectation_eqv_pullback
      S (enrichedLowerFaceObservable G)
  have hreflected : enrichedReflectedFaceBlockedMoment S G ≈
      allCutoffFinePhysicalExpectation S reflectedPullback := by
    unfold enrichedReflectedFaceBlockedMoment reflectedPullback
    exact allCutoffRetainedBlockedExpectation_eqv_pullback
      S (enrichedReflectedFaceObservable G)
  have hrow : enrichedPositiveTimeAverageRowReflectionCovariance S G ≈
      allCutoffFinePhysicalExpectation S jointPullback -
        allCutoffFinePhysicalExpectation S pullbackProduct := by
    unfold enrichedPositiveTimeAverageRowReflectionCovariance
      enrichedPositiveTimeRowReflectionCovariance
      jointPullback pullbackProduct lowerPullback reflectedPullback
    exact allCutoffFinePhysicalExpectation_sub S _ _
  refine Q'.eqv_trans _
    (allCutoffFinePhysicalExpectation S jointPullback -
      allCutoffFinePhysicalExpectation S lowerPullback *
        allCutoffFinePhysicalExpectation S reflectedPullback) _ ?_ ?_
  · unfold enrichedPositiveTimeCenteredReflectionForm
    exact Q'.add_eqv_congr' hjoint
      (Q'.neg_eqv_congr
        _ _ (mul_eqv_both_local hlower hreflected))
  · apply Q'.eqv_symm
    refine Q'.eqv_trans _
      ((allCutoffFinePhysicalExpectation S pullbackProduct -
          allCutoffFinePhysicalExpectation S lowerPullback *
            allCutoffFinePhysicalExpectation S reflectedPullback) +
        (allCutoffFinePhysicalExpectation S jointPullback -
          allCutoffFinePhysicalExpectation S pullbackProduct)) _ ?_ ?_
    · unfold enrichedPositiveTimePulledCenteredReflectionForm
        pullbackProduct lowerPullback reflectedPullback
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) hrow
    · exact covariance_telescope_eqv
        (allCutoffFinePhysicalExpectation S pullbackProduct)
        (allCutoffFinePhysicalExpectation S lowerPullback *
          allCutoffFinePhysicalExpectation S reflectedPullback)
        (allCutoffFinePhysicalExpectation S jointPullback)

/-! ## 2. The retained rows create no conditional covariance -/

/-- A positive incoherent row retains one fixed physical state, so the face
pair is deterministic inside that row and its conditional covariance
vanishes exactly. -/
theorem enrichedPositiveTimeRowReflectionCovariance_eqv_zero_of_incoherent
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hnotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1) :
    enrichedPositiveTimeRowReflectionCovariance S G source ≈ 0 := by
  let lower :=
    (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
      (centralLowerRestriction S.fine.half source.1)
  let reflected :=
    (slabPhysicalFacePositiveUnitObservable G.fineRoot).value
      (centralReflectedUpperRestriction S.fine.half source.1)
  have hjoint : allCutoffRetainedObservablePullback S
        (enrichedLowerReflectedFaceObservable G) source ≈
      lower * reflected :=
    enrichedLowerReflectedFacePullback_eqv_positiveTimeProduct_of_incoherent
      G source hpositive hnotPartition
  have hlower : allCutoffRetainedObservablePullback S
        (enrichedLowerFaceObservable G) source ≈ lower :=
    enrichedLowerFacePullback_eqv_lowerPositiveTime_of_incoherent
      G source hpositive hnotPartition
  have hreflected : allCutoffRetainedObservablePullback S
        (enrichedReflectedFaceObservable G) source ≈ reflected :=
    enrichedReflectedFacePullback_eqv_upperPositiveTime_of_incoherent
      G source hpositive hnotPartition
  unfold enrichedPositiveTimeRowReflectionCovariance
  refine Q'.eqv_trans _ (lower * reflected - lower * reflected) _ ?_ ?_
  · exact Q'.add_eqv_congr' hjoint
      (Q'.neg_eqv_congr
        _ _ (mul_eqv_both_local hlower hreflected))
  · exact Q'.add_neg_self_eqv _

/-! ## 3. Exact localization to coherent rows -/

/-- Conditional covariance in one positive coherent whole-slab recoupling
row. -/
def coherentPositiveTimeRowReflectionCovariance
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) : Q' :=
  coherentLowerReflectedFaceMoment G source hpartition -
    coherentLowerFaceMoment G source hpartition *
      coherentReflectedFaceMoment G source hpartition

def positiveCoherentWeightedRowReflectionCovarianceAux
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    List (SlabPhysicalSourceEntry S.fine) → Q'
  | [] => 0
  | source :: tail =>
      if _hpositive : (0 : Q') < S.fine.physicalTerm source.1 then
        if hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1 then
          S.fine.normalizedMass source.1 *
              coherentPositiveTimeRowReflectionCovariance
                G source hpartition +
            positiveCoherentWeightedRowReflectionCovarianceAux S G tail
        else
          positiveCoherentWeightedRowReflectionCovarianceAux S G tail
      else
        positiveCoherentWeightedRowReflectionCovarianceAux S G tail

/-- The signed conditional correction restricted to its actual support. -/
def positiveCoherentWeightedRowReflectionCovariance
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) : Q' :=
  positiveCoherentWeightedRowReflectionCovarianceAux S G
    (slabPhysicalSourceEntries S.fine)

private theorem coherentRowReflectionCovariance_eqv
    {S : SlabScalePair} (G : EnrichedLowerFaceGeometry S)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1) :
    enrichedPositiveTimeRowReflectionCovariance S G source ≈
      coherentPositiveTimeRowReflectionCovariance G source hpartition := by
  unfold enrichedPositiveTimeRowReflectionCovariance
    coherentPositiveTimeRowReflectionCovariance
  exact Q'.add_eqv_congr'
    (enrichedLowerReflectedFacePullback_eqv_coherentMoment
      G source hpositive hpartition)
    (Q'.neg_eqv_congr
      _ _ (mul_eqv_both_local
        (enrichedLowerFacePullback_eqv_coherentMoment
          G source hpositive hpartition)
        (enrichedReflectedFacePullback_eqv_coherentMoment
          G source hpositive hpartition)))

private theorem weightedRowCovarianceSum_eqv_positiveCoherentAux
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      listQSum
          (fun source =>
            S.fine.normalizedMass source.1 *
              enrichedPositiveTimeRowReflectionCovariance S G source)
          sources ≈
        positiveCoherentWeightedRowReflectionCovarianceAux S G sources
  | [] => Q'.eqv_refl 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [listQSum,
            positiveCoherentWeightedRowReflectionCovarianceAux,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left
              (S.fine.normalizedMass source.1) _ _
              (coherentRowReflectionCovariance_eqv
                G source hpositive hpartition))
            (weightedRowCovarianceSum_eqv_positiveCoherentAux S G tail)
        · simp only [listQSum,
            positiveCoherentWeightedRowReflectionCovarianceAux,
            dif_pos hpositive, dif_neg hpartition]
          have hrowZero :=
            enrichedPositiveTimeRowReflectionCovariance_eqv_zero_of_incoherent
              G source hpositive hpartition
          refine Q'.eqv_trans _
            (0 + positiveCoherentWeightedRowReflectionCovarianceAux
              S G tail) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.eqv_trans _
                (S.fine.normalizedMass source.1 * 0) _
                (Q'.mul_eqv_congr_left
                  (S.fine.normalizedMass source.1) _ _ hrowZero)
                (Q'.mul_zero_eqv _))
              (weightedRowCovarianceSum_eqv_positiveCoherentAux S G tail)
          · exact Q'.eqv_of_eq (Q'.zero_add' _)
      · simp only [listQSum,
          positiveCoherentWeightedRowReflectionCovarianceAux,
          dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + positiveCoherentWeightedRowReflectionCovarianceAux
            S G tail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * enrichedPositiveTimeRowReflectionCovariance
                S G source) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source.1 hpositive))
              (Q'.zero_mul_eqv _))
            (weightedRowCovarianceSum_eqv_positiveCoherentAux S G tail)
        · exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The conditional-covariance correction has no retained-row or Gibbs-null
contribution: it is exactly the positive coherent-row sum. -/
theorem enrichedPositiveTimeAverageRowReflectionCovariance_eqv_positiveCoherent
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S) :
    enrichedPositiveTimeAverageRowReflectionCovariance S G ≈
      positiveCoherentWeightedRowReflectionCovariance S G := by
  unfold enrichedPositiveTimeAverageRowReflectionCovariance
    allCutoffFinePhysicalExpectation
    positiveCoherentWeightedRowReflectionCovariance
  exact weightedRowCovarianceSum_eqv_positiveCoherentAux
    S G (slabPhysicalSourceEntries S.fine)

private theorem positiveCoherentWeightedRowReflectionCovarianceAux_nonnegative
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S)
    (hrow : ∀ (source : SlabPhysicalSourceEntry S.fine)
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1),
      (0 : Q') ≤
        coherentPositiveTimeRowReflectionCovariance
          G source hpartition) :
    ∀ sources : List (SlabPhysicalSourceEntry S.fine),
      (0 : Q') ≤
        positiveCoherentWeightedRowReflectionCovarianceAux S G sources
  | [] => Q'.le_refl' 0
  | source :: tail => by
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source.1
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source.1
        · simp only [positiveCoherentWeightedRowReflectionCovarianceAux,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _
              (S.fine.normalizedMass_nonnegative source.1)
              (hrow source hpositive hpartition))
            (positiveCoherentWeightedRowReflectionCovarianceAux_nonnegative
              S G hrow tail)
        · simp only [positiveCoherentWeightedRowReflectionCovarianceAux,
            dif_pos hpositive, dif_neg hpartition]
          exact positiveCoherentWeightedRowReflectionCovarianceAux_nonnegative
            S G hrow tail
      · simp only [positiveCoherentWeightedRowReflectionCovarianceAux,
          dif_neg hpositive]
        exact positiveCoherentWeightedRowReflectionCovarianceAux_nonnegative
          S G hrow tail

/-- Nonnegative coherent recoupling-row covariance is sufficient for a
nonnegative total conditional correction; retained rows require no premise. -/
theorem enrichedPositiveTimeAverageRowReflectionCovariance_nonnegative_of_coherent
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S)
    (hrow : ∀ (source : SlabPhysicalSourceEntry S.fine)
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1),
      (0 : Q') ≤
        coherentPositiveTimeRowReflectionCovariance
          G source hpartition) :
    (0 : Q') ≤
      enrichedPositiveTimeAverageRowReflectionCovariance S G := by
  have hcoherent : (0 : Q') ≤
      positiveCoherentWeightedRowReflectionCovariance S G := by
    unfold positiveCoherentWeightedRowReflectionCovariance
    exact positiveCoherentWeightedRowReflectionCovarianceAux_nonnegative
      S G hrow (slabPhysicalSourceEntries S.fine)
  exact Q'.le_trans' _ _ _ hcoherent
    (Q'.ge_of_eqv
      (enrichedPositiveTimeAverageRowReflectionCovariance_eqv_positiveCoherent
        S G))

/-- The law of total covariance reduces enriched reflection positivity to
the two honest nonnegative summands. -/
theorem enrichedPositiveTimeCenteredReflectionForm_nonnegative_of_components
    (S : SlabScalePair) (G : EnrichedLowerFaceGeometry S)
    (hpulled : (0 : Q') ≤
      enrichedPositiveTimePulledCenteredReflectionForm S G)
    (hrow : ∀ (source : SlabPhysicalSourceEntry S.fine)
      (_hpositive : (0 : Q') < S.fine.physicalTerm source.1)
      (hpartition : (0 : Q') < wholeSlabRawRowPartition S source.1),
      (0 : Q') ≤
        coherentPositiveTimeRowReflectionCovariance
          G source hpartition) :
    (0 : Q') ≤ enrichedPositiveTimeCenteredReflectionForm S G := by
  have hconditional : (0 : Q') ≤
      enrichedPositiveTimeAverageRowReflectionCovariance S G :=
    enrichedPositiveTimeAverageRowReflectionCovariance_nonnegative_of_coherent
      S G hrow
  have hsum : (0 : Q') ≤
      enrichedPositiveTimePulledCenteredReflectionForm S G +
        enrichedPositiveTimeAverageRowReflectionCovariance S G :=
    Q'.zero_le_add _ _ hpulled hconditional
  exact Q'.le_trans' _ _ _ hsum
    (Q'.ge_of_eqv
      (enrichedPositiveTimeCenteredReflectionForm_eqv_pulled_add_row S G))

/-! ## Axiom audit -/

#print axioms enrichedPositiveTimeCenteredReflectionForm_eqv_pulled_add_row
#print axioms enrichedPositiveTimePulledCenteredReflectionForm_eqv_sameObject
#print axioms enrichedPositiveTimeRowReflectionCovariance_eqv_zero_of_incoherent
#print axioms enrichedPositiveTimeAverageRowReflectionCovariance_eqv_positiveCoherent
#print axioms enrichedPositiveTimeCenteredReflectionForm_nonnegative_of_components

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeTotalCovariance
