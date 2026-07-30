/-
# Core/tail CP domination on the fixed-magnetic BF4 carrier

A uniform relative estimate on every Peter--Weyl label is stronger than the
small-time Yang--Mills analysis naturally provides.  Faraut/Mehler comparison
is uniform on a spacing-dependent interior label window, while the omitted
labels are controlled by heat-kernel tails.

This module proves the exact finite algebra needed for that split.  For a
Boolean core of the common carrier,

* the physical and reference weighted Grams are split exactly into core and
  tail pieces;
* a relative core estimate is propagated by complete positivity;
* the two nonnegative tail row masses are added without a cardinality loss;
* common physical partition normalization is cancelled exactly.

Thus a `1/16` core comparison and two `1/32` tail payments imply the desired
`1/8` normalized row estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination

namespace YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SameCarrierRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact common-carrier decomposition -/

/-- Channels outside a displayed Boolean core. -/
def tailChannels {Channel : Type}
    (channels : List Channel) (core : Channel → Bool) :
    List Channel :=
  channels.filter (fun channel => !(core channel))

/-- One source row of a weighted Gram restricted to the tail carrier. -/
def weightedGramTailRowMass
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (core : Channel → Bool)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (source : State) : Q' :=
  listQSum
    (fun target =>
      weightedGram
        (tailChannels channels core)
        weight amplitude source target)
    states

/-- A weighted Gram is the exact sum of its Boolean core and complement. -/
theorem weightedGram_core_add_tail
    {State Channel : Type}
    (channels : List Channel)
    (core : Channel → Bool)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right : State) :
    weightedGram channels weight amplitude left right ≈
      weightedGram (channels.filter core)
          weight amplitude left right +
        weightedGram (tailChannels channels core)
          weight amplitude left right := by
  unfold weightedGram tailChannels
  exact listQSum_filter_partition
    (fun channel =>
      weight channel *
        (amplitude left channel *
          amplitude right channel))
    core channels

/-- Nonnegative weights and half-amplitudes make every restricted Gram entry
nonnegative. -/
theorem weightedGram_entry_nonnegative
    {State Channel : Type}
    (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right : State)
    (hweight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ weight channel)
    (hleft :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ amplitude left channel)
    (hright :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ amplitude right channel) :
    (0 : Q') ≤
      weightedGram channels weight amplitude left right := by
  unfold weightedGram
  apply listQSum_nonnegative_on
  intro channel hchannel
  exact Q'.mul_nonneg _ _
    (hweight channel hchannel)
    (Q'.mul_nonneg _ _
      (hleft channel hchannel)
      (hright channel hchannel))

private theorem abs_sub_nonnegative_le_add
    (left right : Q')
    (hleft : (0 : Q') ≤ left)
    (hright : (0 : Q') ≤ right) :
    Q'.abs (left + (-right)) ≤ left + right := by
  refine Q'.le_trans' _ _ _
    (abs_add_le left (-right)) ?_
  exact Q'.add_le_add
    (Q'.le_of_eqv (Q'.abs_of_nonneg hleft))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_neg' right))
      (Q'.le_of_eqv (Q'.abs_of_nonneg hright)))

private theorem core_tail_difference_regroup
    (physicalCore physicalTail
      referenceCore referenceTail : Q') :
    (physicalCore + physicalTail) +
        (-(referenceCore + referenceTail)) ≈
      (physicalCore + (-referenceCore)) +
        (physicalTail + (-referenceTail)) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (physicalCore + physicalTail)
      (-(referenceCore + referenceTail))
      ((-referenceCore) + (-referenceTail))
      (Q'.neg_add_eqv referenceCore referenceTail))
    (Q'.add_swap_inner
      physicalCore physicalTail
      (-referenceCore) (-referenceTail))

/-! ## 2. Entry and row core/tail estimates -/

/-- The exact one-entry cutoff estimate.

Only the core uses a relative comparison.  Outside the core the physical and
reference terms are separately nonnegative, so their complete masses pay the
tail without a pointwise ratio. -/
theorem weightedGram_entry_error_le_core_tail
    {State Channel : Type}
    (channels : List Channel)
    (core : Channel → Bool)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coreEpsilon : Q')
    (left right : State)
    (hphysicalWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ physicalWeight channel)
    (hreferenceWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ referenceWeight channel)
    (hleft :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ amplitude left channel)
    (hright :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ amplitude right channel)
    (hcore :
      ∀ channel,
        channel ∈ channels.filter core →
          Q'.abs
              (physicalWeight channel +
                (-referenceWeight channel)) ≤
            coreEpsilon * physicalWeight channel) :
    Q'.abs
        (weightedGram channels physicalWeight amplitude left right +
          (-weightedGram channels referenceWeight amplitude left right)) ≤
      coreEpsilon *
          weightedGram (channels.filter core)
            physicalWeight amplitude left right +
        (weightedGram (tailChannels channels core)
              physicalWeight amplitude left right +
          weightedGram (tailChannels channels core)
              referenceWeight amplitude left right) := by
  let coreChannels := channels.filter core
  let tails := tailChannels channels core
  let physicalCore :=
    weightedGram coreChannels physicalWeight amplitude left right
  let physicalTail :=
    weightedGram tails physicalWeight amplitude left right
  let referenceCore :=
    weightedGram coreChannels referenceWeight amplitude left right
  let referenceTail :=
    weightedGram tails referenceWeight amplitude left right
  have hphysicalSplit :
      weightedGram channels physicalWeight amplitude left right ≈
        physicalCore + physicalTail := by
    exact weightedGram_core_add_tail
      channels core physicalWeight amplitude left right
  have hreferenceSplit :
      weightedGram channels referenceWeight amplitude left right ≈
        referenceCore + referenceTail := by
    exact weightedGram_core_add_tail
      channels core referenceWeight amplitude left right
  have hcoreError :
      Q'.abs (physicalCore + (-referenceCore)) ≤
        coreEpsilon * physicalCore := by
    exact weightedGram_entry_error_le_of_integrand_relative
      coreChannels physicalWeight referenceWeight amplitude
      coreEpsilon left right
      (fun channel hchannel =>
        gramIntegrand_relative_of_weight_relative
          (physicalWeight channel)
          (referenceWeight channel)
          (amplitude left channel)
          (amplitude right channel)
          coreEpsilon
          (hleft channel
            (List.mem_filter.mp hchannel).1)
          (hright channel
            (List.mem_filter.mp hchannel).1)
          (hcore channel hchannel))
  have hphysicalTailNonnegative :
      (0 : Q') ≤ physicalTail := by
    exact weightedGram_entry_nonnegative
      tails physicalWeight amplitude left right
      (fun channel hchannel =>
        hphysicalWeight channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hleft channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hright channel
          (List.mem_filter.mp hchannel).1)
  have hreferenceTailNonnegative :
      (0 : Q') ≤ referenceTail := by
    exact weightedGram_entry_nonnegative
      tails referenceWeight amplitude left right
      (fun channel hchannel =>
        hreferenceWeight channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hleft channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hright channel
          (List.mem_filter.mp hchannel).1)
  have hregroup :
      weightedGram channels physicalWeight amplitude left right +
          (-weightedGram channels referenceWeight amplitude left right) ≈
        (physicalCore + (-referenceCore)) +
          (physicalTail + (-referenceTail)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        hphysicalSplit
        (Q'.neg_eqv_congr _ _ hreferenceSplit))
      (core_tail_difference_regroup
        physicalCore physicalTail
        referenceCore referenceTail)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Constructive.Q'.abs_eqv_congr hregroup)) ?_
  refine Q'.le_trans' _ _ _
    (abs_add_le
      (physicalCore + (-referenceCore))
      (physicalTail + (-referenceTail))) ?_
  exact Q'.add_le_add
    hcoreError
    (abs_sub_nonnegative_le_add
      physicalTail referenceTail
      hphysicalTailNonnegative
      hreferenceTailNonnegative)

/-- Rowwise cutoff domination before normalization. -/
theorem weightedGram_row_error_le_core_tail
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (core : Channel → Bool)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coreEpsilon : Q')
    (source : State)
    (hphysicalWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ physicalWeight channel)
    (hreferenceWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ referenceWeight channel)
    (hamplitude :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          (0 : Q') ≤ amplitude state channel)
    (hsource : source ∈ states)
    (hcore :
      ∀ channel,
        channel ∈ channels.filter core →
          Q'.abs
              (physicalWeight channel +
                (-referenceWeight channel)) ≤
            coreEpsilon * physicalWeight channel) :
    finiteJointDifferenceAbsRowMass
        states
        (weightedGram channels physicalWeight amplitude)
        (weightedGram channels referenceWeight amplitude)
        source ≤
      coreEpsilon *
          listQSum
            (fun target =>
              weightedGram
                (channels.filter core)
                physicalWeight amplitude source target)
            states +
        (weightedGramTailRowMass states channels core
            physicalWeight amplitude source +
          weightedGramTailRowMass states channels core
            referenceWeight amplitude source) := by
  have hentry :
      ∀ target, target ∈ states →
        Q'.abs
            (weightedGram channels physicalWeight amplitude
                  source target +
              (-weightedGram channels referenceWeight amplitude
                  source target)) ≤
          coreEpsilon *
              weightedGram
                (channels.filter core)
                physicalWeight amplitude source target +
            (weightedGram (tailChannels channels core)
                  physicalWeight amplitude source target +
              weightedGram (tailChannels channels core)
                  referenceWeight amplitude source target) := by
    intro target htarget
    exact weightedGram_entry_error_le_core_tail
      channels core physicalWeight referenceWeight
      amplitude coreEpsilon source target
      hphysicalWeight hreferenceWeight
      (hamplitude source hsource)
      (hamplitude target htarget)
      hcore
  unfold finiteJointDifferenceAbsRowMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ states
      (fun target htarget => hentry target htarget)) ?_
  unfold weightedGramTailRowMass
  exact Q'.le_of_eqv (by
    calc
      listQSum
        (fun target =>
          coreEpsilon *
                weightedGram
                  (channels.filter core)
                  physicalWeight amplitude source target +
              (weightedGram (tailChannels channels core)
                    physicalWeight amplitude source target +
                weightedGram (tailChannels channels core)
                    referenceWeight amplitude source target))
        states ≈
        listQSum
          (fun target =>
            coreEpsilon *
              weightedGram
                (channels.filter core)
                physicalWeight amplitude source target)
          states +
        listQSum
          (fun target =>
            weightedGram (tailChannels channels core)
                  physicalWeight amplitude source target +
              weightedGram (tailChannels channels core)
                  referenceWeight amplitude source target)
          states :=
      listQSum_add _ _ states
      _ ≈
        coreEpsilon *
          listQSum
            (fun target =>
              weightedGram
                (channels.filter core)
                physicalWeight amplitude source target)
            states +
        (listQSum
            (fun target =>
              weightedGram (tailChannels channels core)
                physicalWeight amplitude source target)
            states +
          listQSum
            (fun target =>
              weightedGram (tailChannels channels core)
                referenceWeight amplitude source target)
            states) := by
        exact Q'.add_eqv_congr'
          (listQSum_mul_left
            coreEpsilon
            (fun target =>
              weightedGram
                (channels.filter core)
                physicalWeight amplitude source target)
            states)
          (listQSum_add _ _ states))

/-! ## 3. Common normalization and the exact eighth split -/

/-- A core comparison plus two tail payments imply a normalized row-relative
bound with their exact summed budget. -/
theorem normalizedWeightedGram_row_error_le_core_tail
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (core : Channel → Bool)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (partition : Q')
    (partition_pos : (0 : Q') < partition)
    (coreEpsilon physicalTailEpsilon referenceTailEpsilon
      marginal : Q')
    (hcoreEpsilon : (0 : Q') ≤ coreEpsilon)
    (source : State)
    (hphysicalWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ physicalWeight channel)
    (hreferenceWeight :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ referenceWeight channel)
    (hamplitude :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          (0 : Q') ≤ amplitude state channel)
    (hsource : source ∈ states)
    (hphysicalRow :
      listQSum
          (fun target =>
            weightedGram channels physicalWeight amplitude
              source target)
          states ≈
        partition * marginal)
    (hcore :
      ∀ channel,
        channel ∈ channels.filter core →
          Q'.abs
              (physicalWeight channel +
                (-referenceWeight channel)) ≤
            coreEpsilon * physicalWeight channel)
    (hphysicalTail :
      weightedGramTailRowMass states channels core
          physicalWeight amplitude source ≤
        physicalTailEpsilon * (partition * marginal))
    (hreferenceTail :
      weightedGramTailRowMass states channels core
          referenceWeight amplitude source ≤
        referenceTailEpsilon * (partition * marginal)) :
    finiteJointDifferenceAbsRowMass
        states
        (normalizedWeightedGramJoint
          channels physicalWeight amplitude
          partition partition_pos)
        (normalizedWeightedGramJoint
          channels referenceWeight amplitude
          partition partition_pos)
        source ≤
      (coreEpsilon +
          (physicalTailEpsilon + referenceTailEpsilon)) *
        marginal := by
  let physicalCoreRow :=
    listQSum
      (fun target =>
        weightedGram
          (channels.filter core)
          physicalWeight amplitude source target)
      states
  let physicalTail :=
    weightedGramTailRowMass states channels core
      physicalWeight amplitude source
  let referenceTail :=
    weightedGramTailRowMass states channels core
      referenceWeight amplitude source
  have hraw :=
    weightedGram_row_error_le_core_tail
      states channels core physicalWeight referenceWeight
      amplitude coreEpsilon source
      hphysicalWeight hreferenceWeight hamplitude hsource hcore
  have hcoreRowNonnegative :
      (0 : Q') ≤ physicalCoreRow := by
    apply listQSum_nonnegative_on
    intro target htarget
    exact weightedGram_entry_nonnegative
      (channels.filter core)
      physicalWeight amplitude source target
      (fun channel hchannel =>
        hphysicalWeight channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hamplitude source hsource channel
          (List.mem_filter.mp hchannel).1)
      (fun channel hchannel =>
        hamplitude target htarget channel
          (List.mem_filter.mp hchannel).1)
  have hcoreRowLe :
      physicalCoreRow ≤ partition * marginal := by
    have htailNonnegative :
        (0 : Q') ≤ physicalTail := by
      unfold physicalTail weightedGramTailRowMass
      apply listQSum_nonnegative_on
      intro target htarget
      exact weightedGram_entry_nonnegative
        (tailChannels channels core)
        physicalWeight amplitude source target
        (fun channel hchannel =>
          hphysicalWeight channel
            (List.mem_filter.mp hchannel).1)
        (fun channel hchannel =>
          hamplitude source hsource channel
            (List.mem_filter.mp hchannel).1)
        (fun channel hchannel =>
          hamplitude target htarget channel
            (List.mem_filter.mp hchannel).1)
    have hsplit :
        listQSum
            (fun target =>
              weightedGram channels physicalWeight amplitude
                source target)
            states ≈
          physicalCoreRow + physicalTail := by
      exact Q'.eqv_trans _ _ _
        (listQSum_congr
          (fun target =>
            weightedGram_core_add_tail
              channels core physicalWeight amplitude
              source target)
          states)
        (listQSum_add _ _ states)
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        physicalCoreRow physicalTail htailNonnegative)
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm hsplit)
          hphysicalRow))
  have hcoreScaled :
      coreEpsilon * physicalCoreRow ≤
        coreEpsilon * (partition * marginal) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hcoreRowLe
      hcoreEpsilon
  have hrawBudget :
      finiteJointDifferenceAbsRowMass
          states
          (weightedGram channels physicalWeight amplitude)
          (weightedGram channels referenceWeight amplitude)
          source ≤
        (coreEpsilon +
            (physicalTailEpsilon + referenceTailEpsilon)) *
          (partition * marginal) := by
    refine Q'.le_trans' _ _ _ hraw ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hcoreScaled
        (Q'.add_le_add hphysicalTail hreferenceTail)) ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (coreEpsilon * (partition * marginal))
          (physicalTailEpsilon * (partition * marginal) +
            referenceTailEpsilon * (partition * marginal))
          ((physicalTailEpsilon + referenceTailEpsilon) *
            (partition * marginal))
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              physicalTailEpsilon referenceTailEpsilon
              (partition * marginal))))
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            coreEpsilon
            (physicalTailEpsilon + referenceTailEpsilon)
            (partition * marginal))))
  let reciprocal := Q'.recipPos partition partition_pos
  have hreciprocalNonnegative :
      (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt (Q'.recipPos_pos partition partition_pos)
  have hnormalized :
      finiteJointDifferenceAbsRowMass
          states
          (normalizedWeightedGramJoint
            channels physicalWeight amplitude
            partition partition_pos)
          (normalizedWeightedGramJoint
            channels referenceWeight amplitude
            partition partition_pos)
          source ≈
        finiteJointDifferenceAbsRowMass
            states
            (weightedGram channels physicalWeight amplitude)
            (weightedGram channels referenceWeight amplitude)
            source * reciprocal := by
    unfold finiteJointDifferenceAbsRowMass
      normalizedWeightedGramJoint Q'.divPos reciprocal
    refine Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun target =>
          Q'.eqv_trans _ _ _
            (YMGap.Constructive.Q'.abs_eqv_congr
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left
                  (weightedGram channels physicalWeight amplitude
                      source target * reciprocal)
                  (-(weightedGram channels referenceWeight amplitude
                      source target * reciprocal))
                  ((-weightedGram channels referenceWeight amplitude
                      source target) * reciprocal)
                  (Q'.eqv_symm
                    (Q'.neg_mul_eqv _ _)))
                (Q'.eqv_symm
                  (Q'.add_mul_eqv _ _ reciprocal))))
            (abs_mul_nonneg_right _ hreciprocalNonnegative))
        states) ?_
    exact listQSum_mul_right _ reciprocal states
  have hscaled :
      finiteJointDifferenceAbsRowMass
            states
            (weightedGram channels physicalWeight amplitude)
            (weightedGram channels referenceWeight amplitude)
            source * reciprocal ≤
        ((coreEpsilon +
            (physicalTailEpsilon + referenceTailEpsilon)) *
          (partition * marginal)) * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hrawBudget hreciprocalNonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hnormalized)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        let total :=
          coreEpsilon +
            (physicalTailEpsilon + referenceTailEpsilon)
        calc
          (total * (partition * marginal)) * reciprocal ≈
              total *
                ((partition * marginal) * reciprocal) :=
            Q'.mul_assoc_eqv _ _ _
          _ ≈ total *
                (partition * (marginal * reciprocal)) :=
            Q'.mul_eqv_congr_left total _ _
              (Q'.mul_assoc_eqv partition marginal reciprocal)
          _ ≈ total *
                (partition * (reciprocal * marginal)) :=
            Q'.mul_eqv_congr_left total _ _
              (Q'.mul_eqv_congr_left partition _ _
                (Q'.mul_comm_eqv marginal reciprocal))
          _ ≈ total *
                ((partition * reciprocal) * marginal) :=
            Q'.mul_eqv_congr_left total _ _
              (Q'.eqv_symm
                (Q'.mul_assoc_eqv
                  partition reciprocal marginal))
          _ ≈ total * (1 * marginal) :=
            Q'.mul_eqv_congr_left total _ _
              (Q'.mul_eqv_congr_right _ _ marginal
                (Q'.mul_recipPos_eqv
                  partition partition_pos))
          _ ≈ total * marginal :=
            Q'.mul_eqv_congr_left total _ _
              (Q'.one_mul_eqv marginal))))

/-- Exact dyadic allocation:
`1/16 + 1/32 + 1/32 = 1/8`. -/
theorem sixteenth_add_two_thirtySeconds_eqv_eighth :
    Q'.mkPos 1 16 (by decide) +
        (Q'.mkPos 1 32 (by decide) +
          Q'.mkPos 1 32 (by decide)) ≈
      Q'.mkPos 1 8 (by decide) := by
  decide

/-! ## 4. Literal BF4 specialization -/

/-- Spacing-dependent core/tail data on the genuine enlarged BF4 carrier.

Unlike a global Harnack window, the two tail fields are row estimates and may
be proved by an all-label regrouping or a spacing-dependent cutoff modulus. -/
structure CentralFixedMagneticCoreTailEighthData
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q') : Type where
  core :
    EdgeLabelling →
      CentralFixedMagneticIntertwinerChannel → Bool
  reference_nonnegative :
    ∀ channel,
      channel ∈
          centralFixedMagneticIntertwinerChannels K half →
        (0 : Q') ≤ referenceWeight channel
  core_relative_sixteenth :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
      ∀ channel,
      channel ∈
          (centralFixedMagneticIntertwinerChannels K half).filter
            (core source) →
        Q'.abs
            (centralFixedMagneticIntertwinerWeight w half channel +
              (-referenceWeight channel)) ≤
          Q'.mkPos 1 16 (by decide) *
            centralFixedMagneticIntertwinerWeight w half channel
  physical_tail_thirtySecond :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        weightedGramTailRowMass
            (centralPositiveHalfStates w hw K half)
            (centralFixedMagneticIntertwinerChannels K half)
            (core source)
            (centralFixedMagneticIntertwinerWeight w half)
            (centralFixedMagneticIntertwinerHalfAmplitude
              w K half)
            source ≤
          Q'.mkPos 1 32 (by decide) *
            (slabParametricKPhysicalPartition
                w K (centralExtent half) *
              centralPhysicalRowMarginal
                w hw K half source)
  reference_tail_thirtySecond :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        weightedGramTailRowMass
            (centralPositiveHalfStates w hw K half)
            (centralFixedMagneticIntertwinerChannels K half)
            (core source) referenceWeight
            (centralFixedMagneticIntertwinerHalfAmplitude
              w K half)
            source ≤
          Q'.mkPos 1 32 (by decide) *
            (slabParametricKPhysicalPartition
                w K (centralExtent half) *
              centralPhysicalRowMarginal
                w hw K half source)

namespace CentralFixedMagneticCoreTailEighthData

/-- The spacing-dependent core/tail data prove the literal normalized
physical-minus-reference row eighth. -/
theorem normalized_row_error_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q'}
    (data :
      CentralFixedMagneticCoreTailEighthData
        hw K half referenceWeight)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedFixedMagneticReferenceGram
          w hw K half referenceWeight)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  let states := centralPositiveHalfStates w hw K half
  let channels := centralFixedMagneticIntertwinerChannels K half
  let physicalWeight :=
    centralFixedMagneticIntertwinerWeight w half
  let amplitude :=
    centralFixedMagneticIntertwinerHalfAmplitude w K half
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  have hphysical :
      finiteJointDifferenceAbsRowMass
          states
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half referenceWeight)
          source ≈
        finiteJointDifferenceAbsRowMass
          states
          (normalizedWeightedGramJoint
            channels physicalWeight amplitude
            partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent half)))
          (normalizedWeightedGramJoint
            channels referenceWeight amplitude
            partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent half)))
          source := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply YMGap.Constructive.Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_right
    exact centralNormalizedPhysical_eqv_fixedMagneticGram
      hsource htarget
  have hbound :=
    normalizedWeightedGram_row_error_le_core_tail
      states channels (data.core source)
      physicalWeight referenceWeight amplitude
      partition
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      (Q'.mkPos 1 16 (by decide))
      (Q'.mkPos 1 32 (by decide))
      (Q'.mkPos 1 32 (by decide))
      (centralPhysicalRowMarginal w hw K half source)
      (by decide)
      source
      (fun channel _ =>
        centralFixedMagneticIntertwinerWeight_nonnegative
          hw half channel)
      data.reference_nonnegative
      (fun state _ channel _ => by
        unfold amplitude
          centralFixedMagneticIntertwinerHalfAmplitude
        exact centralHalfAmplitude_nonnegative
          hw K half state channel.1)
      hsource
      (centralFixedMagneticPhysicalGram_positiveRow_eqv_partition_mul_marginal
        hsource)
      (data.core_relative_sixteenth source hsource)
      (data.physical_tail_thirtySecond source hsource)
      (data.reference_tail_thirtySecond source hsource)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hphysical)
    (Q'.le_trans' _ _ _ hbound
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _
          (centralPhysicalRowMarginal w hw K half source)
          sixteenth_add_two_thirtySeconds_eqv_eighth)))

end CentralFixedMagneticCoreTailEighthData

end YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination.weightedGram_core_add_tail
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination.weightedGram_entry_error_le_core_tail
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination.weightedGram_row_error_le_core_tail
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination.normalizedWeightedGram_row_error_le_core_tail
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination.CentralFixedMagneticCoreTailEighthData.normalized_row_error_le_eighth
