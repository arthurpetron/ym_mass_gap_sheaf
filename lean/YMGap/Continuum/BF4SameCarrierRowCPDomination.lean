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
