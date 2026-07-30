/-
# Same-carrier CP order gives BF4 row-relative domination

The magnetically enlarged BF4 carrier puts the physical kernel and a
reference kernel on one literal channel list with one literal half-amplitude.
The analytic estimate then arrives channel by channel.  This module proves
that such a pointwise relative estimate survives:

1. the signed channel sum defining one Gram entry;
2. the absolute value of the entry difference; and
3. the complete retained target-row sum.

The resulting bound is paid by the physical source row mass itself.  There
is no carrier-cardinality factor and no inverse minimum marginal.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4WeightedJointPerronPerturbation
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.BF4SameCarrierRowCPDomination

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_on
    {A : Type} (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
        listQSum lower items ≤ listQSum upper items
  | [], _ =>
      Q'.le_refl' 0
  | head :: tail, hterm => by
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun item hitem =>
            hterm item
              (List.mem_cons_of_mem head hitem)))

/-- A relative estimate on two channel weights survives multiplication by a
nonnegative common half-amplitude product.  This is the scalar CP-order step
which turns a Yang--Mills heat-weight estimate into the integrand hypothesis
used below. -/
theorem gramIntegrand_relative_of_weight_relative
    (physicalWeight referenceWeight
      leftAmplitude rightAmplitude epsilon : Q')
    (hleft : (0 : Q') ≤ leftAmplitude)
    (hright : (0 : Q') ≤ rightAmplitude)
    (hweight :
      Q'.abs (physicalWeight + (-referenceWeight)) ≤
        epsilon * physicalWeight) :
    Q'.abs
        (physicalWeight *
              (leftAmplitude * rightAmplitude) +
          (-(referenceWeight *
              (leftAmplitude * rightAmplitude)))) ≤
      epsilon *
        (physicalWeight *
          (leftAmplitude * rightAmplitude)) := by
  let amplitudeProduct :=
    leftAmplitude * rightAmplitude
  have hamplitudeProduct :
      (0 : Q') ≤ amplitudeProduct :=
    Q'.mul_nonneg _ _ hleft hright
  have hdifference :
      physicalWeight * amplitudeProduct +
          (-(referenceWeight * amplitudeProduct)) ≈
        (physicalWeight + (-referenceWeight)) *
          amplitudeProduct := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (physicalWeight * amplitudeProduct)
        (-(referenceWeight * amplitudeProduct))
        ((-referenceWeight) * amplitudeProduct)
        (Q'.eqv_symm
          (Q'.neg_mul_eqv referenceWeight amplitudeProduct)))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          physicalWeight (-referenceWeight)
          amplitudeProduct))
  have habs :
      Q'.abs
          (physicalWeight * amplitudeProduct +
            (-(referenceWeight * amplitudeProduct))) ≈
        Q'.abs (physicalWeight + (-referenceWeight)) *
          amplitudeProduct := by
    exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr hdifference)
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (physicalWeight + (-referenceWeight))
        hamplitudeProduct)
  have hscaled :
      Q'.abs (physicalWeight + (-referenceWeight)) *
          amplitudeProduct ≤
        (epsilon * physicalWeight) *
          amplitudeProduct :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hweight hamplitudeProduct
  have hreassociate :
      (epsilon * physicalWeight) * amplitudeProduct ≈
        epsilon *
          (physicalWeight * amplitudeProduct) :=
    Q'.mul_assoc_eqv
      epsilon physicalWeight amplitudeProduct
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _
      hscaled (Q'.le_of_eqv hreassociate))

/-- The concrete multiplicative window `[7/8, 9/8]` is exactly the relative
`1/8` absolute-error estimate. -/
theorem weightRelativeEighth_of_sevenNineWindow
    (physicalWeight referenceWeight : Q')
    (hlower :
      Q'.mkPos 7 8 (by decide) * physicalWeight ≤
        referenceWeight)
    (hupper :
      referenceWeight ≤
        Q'.mkPos 9 8 (by decide) * physicalWeight) :
    Q'.abs (physicalWeight + (-referenceWeight)) ≤
      Q'.mkPos 1 8 (by decide) * physicalWeight := by
  let epsilon := Q'.mkPos 1 8 (by decide)
  have hsplitLower :
      Q'.mkPos 7 8 (by decide) * physicalWeight +
          epsilon * physicalWeight ≈
        physicalWeight := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (Q'.mkPos 7 8 (by decide))
          epsilon physicalWeight))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ physicalWeight
          (by decide))
        (Q'.one_mul_eqv physicalWeight))
  have hsplitUpper :
      Q'.mkPos 9 8 (by decide) * physicalWeight ≈
        physicalWeight + epsilon * physicalWeight := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.mkPos 9 8 (by decide))
        (1 + epsilon) physicalWeight
        (by decide))
      (Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv
          1 epsilon physicalWeight)
        (Q'.add_eqv_congr_right
          (1 * physicalWeight)
          physicalWeight
          (epsilon * physicalWeight)
          (Q'.one_mul_eqv physicalWeight)))
  have hphysical_le :
      physicalWeight ≤
        referenceWeight + epsilon * physicalWeight := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsplitLower)
      (Q'.add_le_add_right _ _ _
        hlower)
  have hreference_le :
      referenceWeight ≤
        physicalWeight + epsilon * physicalWeight := by
    exact Q'.le_trans' _ _ _
      hupper (Q'.le_of_eqv hsplitUpper)
  exact Q'.abs_le
    (Q'.neg_le_sub_of_le_add hreference_le)
    (Q'.sub_le_of_le_add hphysical_le)

/-- A channel-weight relative estimate implies the full common-carrier
integrand estimate whenever all retained half-amplitudes are nonnegative. -/
theorem weightedGram_integrand_relative_of_weight_relative
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (epsilon : Q')
    (hamplitude :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          (0 : Q') ≤ amplitude state channel)
    (hweight :
      ∀ channel, channel ∈ channels →
        Q'.abs
            (physicalWeight channel +
              (-referenceWeight channel)) ≤
          epsilon * physicalWeight channel) :
    ∀ left, left ∈ states →
      ∀ right, right ∈ states →
        ∀ channel, channel ∈ channels →
          Q'.abs
              (physicalWeight channel *
                    (amplitude left channel *
                      amplitude right channel) +
                (-(referenceWeight channel *
                    (amplitude left channel *
                      amplitude right channel)))) ≤
            epsilon *
              (physicalWeight channel *
                (amplitude left channel *
                  amplitude right channel)) := by
  intro left hleft right hright channel hchannel
  exact gramIntegrand_relative_of_weight_relative
    (physicalWeight channel)
    (referenceWeight channel)
    (amplitude left channel)
    (amplitude right channel)
    epsilon
    (hamplitude left hleft channel hchannel)
    (hamplitude right hright channel hchannel)
    (hweight channel hchannel)

/-- A channelwise relative CP-order estimate implies the corresponding
relative estimate for one common-carrier weighted-Gram entry.

The hypothesis is stated on the actual integrands.  This is the form
produced by a positive weight window after the spatial/intertwiner fibers
have been retained rather than prematurely integrated out. -/
theorem weightedGram_entry_error_le_of_integrand_relative
    {State Channel : Type}
    (channels : List Channel)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (epsilon : Q')
    (left right : State)
    (hintegrand :
      ∀ channel,
        channel ∈ channels →
          Q'.abs
              (physicalWeight channel *
                    (amplitude left channel *
                      amplitude right channel) +
                (-(referenceWeight channel *
                    (amplitude left channel *
                      amplitude right channel)))) ≤
            epsilon *
              (physicalWeight channel *
                (amplitude left channel *
                  amplitude right channel))) :
    Q'.abs
        (weightedGram
            channels physicalWeight amplitude left right +
          (-weightedGram
            channels referenceWeight amplitude left right)) ≤
      epsilon *
        weightedGram
          channels physicalWeight amplitude left right := by
  let physicalTerm :=
    fun channel =>
      physicalWeight channel *
        (amplitude left channel * amplitude right channel)
  let referenceTerm :=
    fun channel =>
      referenceWeight channel *
        (amplitude left channel * amplitude right channel)
  have htriangle :
      Q'.abs
          (listQSum physicalTerm channels +
            (-listQSum referenceTerm channels)) ≤
        listQSum
          (fun channel =>
            Q'.abs
              (physicalTerm channel +
                (-referenceTerm channel)))
          channels :=
    abs_listQSum_sub_le
      physicalTerm referenceTerm channels
  have hsum :
      listQSum
          (fun channel =>
            Q'.abs
              (physicalTerm channel +
                (-referenceTerm channel)))
          channels ≤
        listQSum
          (fun channel =>
            epsilon * physicalTerm channel)
          channels := by
    exact listQSum_mono_on _ _ channels
      (fun channel hchannel =>
        hintegrand channel hchannel)
  have hfactor :
      listQSum
          (fun channel =>
            epsilon * physicalTerm channel)
          channels ≈
        epsilon * listQSum physicalTerm channels :=
    listQSum_mul_left
      epsilon physicalTerm channels
  unfold weightedGram
  exact Q'.le_trans' _ _ _
    htriangle
    (Q'.le_trans' _ _ _
      hsum (Q'.le_of_eqv hfactor))

/-- **All-target same-carrier row domination.**

If every channel integrand differs from its reference by at most an
`epsilon` fraction of the physical integrand, then the complete absolute
row discrepancy is bounded by `epsilon` times the physical row mass.  This
is precisely the source-dependent estimate needed before normalization. -/
theorem weightedGram_row_error_le_of_integrand_relative
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (epsilon : Q')
    (source : State)
    (hintegrand :
      ∀ target,
        target ∈ states →
          ∀ channel,
            channel ∈ channels →
              Q'.abs
                  (physicalWeight channel *
                        (amplitude source channel *
                          amplitude target channel) +
                    (-(referenceWeight channel *
                        (amplitude source channel *
                          amplitude target channel)))) ≤
                epsilon *
                  (physicalWeight channel *
                    (amplitude source channel *
                      amplitude target channel))) :
    finiteJointDifferenceAbsRowMass
        states
        (weightedGram
          channels physicalWeight amplitude)
        (weightedGram
          channels referenceWeight amplitude)
        source ≤
      epsilon *
        listQSum
          (fun target =>
            weightedGram
              channels physicalWeight amplitude
              source target)
          states := by
  have hrows :
      listQSum
          (fun target =>
            Q'.abs
              (weightedGram
                    channels physicalWeight amplitude
                    source target +
                (-weightedGram
                    channels referenceWeight amplitude
                    source target)))
          states ≤
        listQSum
          (fun target =>
            epsilon *
              weightedGram
                channels physicalWeight amplitude
                source target)
          states := by
    exact listQSum_mono_on _ _ states
      (fun target htarget =>
        weightedGram_entry_error_le_of_integrand_relative
          channels physicalWeight referenceWeight
          amplitude epsilon source target
          (hintegrand target htarget))
  unfold finiteJointDifferenceAbsRowMass
  exact Q'.le_trans' _ _ _
    hrows
    (Q'.le_of_eqv
      (listQSum_mul_left
        epsilon
        (fun target =>
          weightedGram
            channels physicalWeight amplitude
            source target)
        states))

/-! ## 2. Common positive partition normalization -/

/-- Normalize a finite weighted Gram by a supplied strictly positive common
partition. -/
def normalizedWeightedGramJoint
    {State Channel : Type}
    (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (partition : Q')
    (partition_pos : (0 : Q') < partition)
    (left right : State) : Q' :=
  Q'.divPos
    (weightedGram channels weight amplitude left right)
    partition partition_pos

/-- Common partition normalization preserves the sharp relative row bound.

The only normalization datum needed is the exact physical row identity

`sum_y Gram_phys(x,y) = partition * marginal(x)`.

Thus a later BF4 specialization may derive this equality from the physical
Choi law and does not pay a global marginal floor. -/
theorem normalizedWeightedGram_row_error_le_of_integrand_relative
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (physicalWeight referenceWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (partition : Q')
    (partition_pos : (0 : Q') < partition)
    (epsilon marginal : Q')
    (source : State)
    (hphysicalRow :
      listQSum
          (fun target =>
            weightedGram
              channels physicalWeight amplitude
              source target)
          states ≈
        partition * marginal)
    (hintegrand :
      ∀ target,
        target ∈ states →
          ∀ channel,
            channel ∈ channels →
              Q'.abs
                  (physicalWeight channel *
                        (amplitude source channel *
                          amplitude target channel) +
                    (-(referenceWeight channel *
                        (amplitude source channel *
                          amplitude target channel)))) ≤
                epsilon *
                  (physicalWeight channel *
                    (amplitude source channel *
                      amplitude target channel))) :
    finiteJointDifferenceAbsRowMass
        states
        (normalizedWeightedGramJoint
          channels physicalWeight amplitude
          partition partition_pos)
        (normalizedWeightedGramJoint
          channels referenceWeight amplitude
          partition partition_pos)
        source ≤
      epsilon * marginal := by
  let physical :=
    fun left right =>
      weightedGram
        channels physicalWeight amplitude left right
  let reference :=
    fun left right =>
      weightedGram
        channels referenceWeight amplitude left right
  let reciprocal :=
    Q'.recipPos partition partition_pos
  have hreciprocal_nonnegative :
      (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt
      (Q'.recipPos_pos partition partition_pos)
  have hentry :
      ∀ target,
        Q'.abs
            (normalizedWeightedGramJoint
                  channels physicalWeight amplitude
                  partition partition_pos source target +
              (-normalizedWeightedGramJoint
                  channels referenceWeight amplitude
                  partition partition_pos source target)) ≈
          Q'.abs
              (physical source target +
                (-reference source target)) *
            reciprocal := by
    intro target
    have hdifference :
        normalizedWeightedGramJoint
              channels physicalWeight amplitude
              partition partition_pos source target +
            (-normalizedWeightedGramJoint
              channels referenceWeight amplitude
              partition partition_pos source target) ≈
          (physical source target +
              (-reference source target)) *
            reciprocal := by
      unfold normalizedWeightedGramJoint
        Q'.divPos physical reference reciprocal
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (weightedGram
            channels physicalWeight amplitude
            source target * reciprocal)
          (-(weightedGram
            channels referenceWeight amplitude
            source target * reciprocal))
          ((-weightedGram
            channels referenceWeight amplitude
            source target) * reciprocal)
          (Q'.eqv_symm
            (Q'.neg_mul_eqv
              (weightedGram
                channels referenceWeight amplitude
                source target)
              reciprocal)))
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            (weightedGram
              channels physicalWeight amplitude
              source target)
            (-weightedGram
              channels referenceWeight amplitude
              source target)
            reciprocal))
    exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr hdifference)
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (physical source target +
          (-reference source target))
        hreciprocal_nonnegative)
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
            states physical reference source *
          reciprocal := by
    unfold finiteJointDifferenceAbsRowMass
    exact Q'.eqv_trans _ _ _
      (listQSum_congr hentry states)
      (listQSum_mul_right
        (fun target =>
          Q'.abs
            (physical source target +
              (-reference source target)))
        reciprocal states)
  have hraw :=
    weightedGram_row_error_le_of_integrand_relative
      states channels physicalWeight referenceWeight
      amplitude epsilon source hintegrand
  have hscaled :
      finiteJointDifferenceAbsRowMass
            states physical reference source *
          reciprocal ≤
        (epsilon *
          listQSum
            (fun target =>
              physical source target)
            states) *
          reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hraw hreciprocal_nonnegative
  have hright :
      (epsilon *
          listQSum
            (fun target =>
              physical source target)
            states) *
          reciprocal ≈
        epsilon * marginal := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (epsilon *
          listQSum
            (fun target =>
              physical source target)
            states)
        (epsilon * (partition * marginal))
        reciprocal
        (Q'.mul_eqv_congr_left
          epsilon _ _ hphysicalRow)) ?_
    calc
      (epsilon * (partition * marginal)) *
            reciprocal ≈
          epsilon *
            ((partition * marginal) * reciprocal) :=
        Q'.mul_assoc_eqv _ _ _
      _ ≈ epsilon *
            (partition * (marginal * reciprocal)) :=
        Q'.mul_eqv_congr_left epsilon _ _
          (Q'.mul_assoc_eqv
            partition marginal reciprocal)
      _ ≈ epsilon *
            (partition * (reciprocal * marginal)) :=
        Q'.mul_eqv_congr_left epsilon _ _
          (Q'.mul_eqv_congr_left partition _ _
            (Q'.mul_comm_eqv marginal reciprocal))
      _ ≈ epsilon *
            ((partition * reciprocal) * marginal) :=
        Q'.mul_eqv_congr_left epsilon _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              partition reciprocal marginal))
      _ ≈ epsilon * (1 * marginal) :=
        Q'.mul_eqv_congr_left epsilon _ _
          (Q'.mul_eqv_congr_right _ _ marginal
            (Q'.mul_recipPos_eqv
              partition partition_pos))
      _ ≈ epsilon * marginal :=
        Q'.mul_eqv_congr_left epsilon _ _
          (Q'.one_mul_eqv marginal)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hnormalized)
    (Q'.le_trans' _ _ _
      hscaled (Q'.le_of_eqv hright))

end YMGap.Continuum.BF4SameCarrierRowCPDomination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.weightedGram_entry_error_le_of_integrand_relative
#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.weightedGram_row_error_le_of_integrand_relative
#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.normalizedWeightedGram_row_error_le_of_integrand_relative
#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.gramIntegrand_relative_of_weight_relative
#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.weightRelativeEighth_of_sevenNineWindow
#print axioms YMGap.Continuum.BF4SameCarrierRowCPDomination.weightedGram_integrand_relative_of_weight_relative
