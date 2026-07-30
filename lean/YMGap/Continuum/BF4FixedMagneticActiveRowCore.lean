/-
# The active-row core removes both BF4 Gram tails exactly

On a common weighted-Gram carrier, a channel contributes to a source row
only through the source half-amplitude.  Define the source-dependent core by
strict positivity of that amplitude.  The physical BF4 half-amplitudes are
nonnegative, so every channel outside this core has amplitude exactly zero.

Consequently both the physical and reference tail rows vanish identically.
This is the direct all-label regrouping alternative to a spacing-dependent
absolute label cutoff.  It inhabits both `1/32` fields of
`CentralFixedMagneticCoreTailEighthData`; the only remaining quantitative
input is a `1/16` relative weight comparison on physically active channels.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility

namespace YMGap.Continuum.BF4FixedMagneticActiveRowCore

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility
open YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The exact physically active channel core for one source row. -/
def centralFixedMagneticActiveCore
    (w : Q') (K half : Nat)
    (source : EdgeLabelling)
    (channel : CentralFixedMagneticIntertwinerChannel) : Bool :=
  decide
    ((0 : Q') <
      centralFixedMagneticIntertwinerHalfAmplitude
        w K half source channel)

private theorem q_nonpositive_of_not_positive
    {q : Q'} (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤
    (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_not_positive
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnot : ¬ (0 : Q') < q) :
    q ≈ 0 := by
  have hnonpositive : q ≤ 0 :=
    q_nonpositive_of_not_positive hnot
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

theorem source_amplitude_eqv_zero_of_tail
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {source : EdgeLabelling}
    {channel : CentralFixedMagneticIntertwinerChannel}
    (hchannel :
      channel ∈
        tailChannels
          (centralFixedMagneticIntertwinerChannels K half)
          (centralFixedMagneticActiveCore
            w K half source)) :
    centralFixedMagneticIntertwinerHalfAmplitude
        w K half source channel ≈
      0 := by
  have htail :=
    (List.mem_filter.mp hchannel).2
  have hinactive :
      centralFixedMagneticActiveCore
          w K half source channel = false := by
    cases hcore :
        centralFixedMagneticActiveCore
          w K half source channel with
    | false => rfl
    | true =>
        simp only [hcore, Bool.not_true,
          Bool.false_eq_true] at htail
  have hnot :
      ¬ (0 : Q') <
        centralFixedMagneticIntertwinerHalfAmplitude
          w K half source channel := by
    unfold centralFixedMagneticActiveCore at hinactive
    simpa only [decide_eq_false_iff_not] using hinactive
  exact q_eqv_zero_of_nonnegative_of_not_positive
    (by
      unfold centralFixedMagneticIntertwinerHalfAmplitude
      exact centralHalfAmplitude_nonnegative
        hw K half source channel.1)
    hnot

/-- Every entry of either shared-amplitude tail Gram is exactly zero.  No
sign condition on the channel weight is needed. -/
theorem activeTail_weightedGram_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (weight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (source target : EdgeLabelling) :
    weightedGram
        (tailChannels
          (centralFixedMagneticIntertwinerChannels K half)
          (centralFixedMagneticActiveCore
            w K half source))
        weight
        (centralFixedMagneticIntertwinerHalfAmplitude
          w K half)
        source target ≈
      0 := by
  let tails :=
    tailChannels
      (centralFixedMagneticIntertwinerChannels K half)
      (centralFixedMagneticActiveCore w K half source)
  unfold weightedGram
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (fun channel =>
        weight channel *
          (centralFixedMagneticIntertwinerHalfAmplitude
              w K half source channel *
            centralFixedMagneticIntertwinerHalfAmplitude
              w K half target channel))
      (fun _ => (0 : Q'))
      tails
      (fun channel hchannel => by
        have hsourceZero :=
          source_amplitude_eqv_zero_of_tail
            (hw := hw) hchannel
        calc
          weight channel *
              (centralFixedMagneticIntertwinerHalfAmplitude
                  w K half source channel *
                centralFixedMagneticIntertwinerHalfAmplitude
                  w K half target channel) ≈
            weight channel *
              (0 *
                centralFixedMagneticIntertwinerHalfAmplitude
                  w K half target channel) :=
            Q'.mul_eqv_congr_left
              (weight channel) _ _
              (Q'.mul_eqv_congr_right _ _ _
                hsourceZero)
          _ ≈ weight channel * 0 :=
            Q'.mul_eqv_congr_left
              (weight channel) _ _
              (Q'.zero_mul_eqv _)
          _ ≈ (0 : Q') :=
            Q'.mul_zero_eqv _))
    (listQSum_zero tails)

/-- The complete active-complement source row is exactly zero. -/
theorem activeTail_weightedGramRowMass_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (weight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (source : EdgeLabelling) :
    weightedGramTailRowMass
        (centralPositiveHalfStates w hw K half)
        (centralFixedMagneticIntertwinerChannels K half)
        (centralFixedMagneticActiveCore w K half source)
        weight
        (centralFixedMagneticIntertwinerHalfAmplitude
          w K half)
        source ≈
      0 := by
  unfold weightedGramTailRowMass
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target =>
        activeTail_weightedGram_eqv_zero
          (hw := hw) weight source target)
      (centralPositiveHalfStates w hw K half))
    (listQSum_zero
      (centralPositiveHalfStates w hw K half))

/-- The direct all-label active-core constructor.  Both tail obligations are
proved, rather than retained as fields. -/
def activeCoreTailEighthData
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (hreference :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels K half →
          (0 : Q') ≤ referenceWeight channel)
    (hactive :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
        ∀ channel,
          channel ∈
              (centralFixedMagneticIntertwinerChannels K half).filter
                (centralFixedMagneticActiveCore
                  w K half source) →
            Q'.abs
                (centralFixedMagneticIntertwinerWeight
                      w half channel +
                  (-referenceWeight channel)) ≤
              Q'.mkPos 1 16 (by decide) *
                centralFixedMagneticIntertwinerWeight
                  w half channel) :
    CentralFixedMagneticCoreTailEighthData
      hw K half referenceWeight where
  core := centralFixedMagneticActiveCore w K half
  reference_nonnegative := hreference
  core_relative_sixteenth := hactive
  physical_tail_thirtySecond := by
    intro source hsource
    have hzero :=
      activeTail_weightedGramRowMass_eqv_zero
        (hw := hw)
        (K := K) (half := half)
        (centralFixedMagneticIntertwinerWeight w half)
        source
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hzero) ?_
    exact Q'.mul_nonneg _ _
      (by decide)
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent half)))
        (centralPhysicalRowMarginal_nonnegative
          hw K half source))
  reference_tail_thirtySecond := by
    intro source hsource
    have hzero :=
      activeTail_weightedGramRowMass_eqv_zero
        (hw := hw) (K := K) (half := half)
        referenceWeight source
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hzero) ?_
    exact Q'.mul_nonneg _ _
      (by decide)
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent half)))
        (centralPhysicalRowMarginal_nonnegative
          hw K half source))

/-! ## Exact endpoint assembly -/

/-- An exact same-carrier Peter--Weyl identification and a `1/16` comparison
on physically active channels now suffice for the complete endpoint
realization; both row tails are constructed above. -/
def activeCoreEndpointRealization
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint w hw K half)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (hjoint :
      ∀ left,
        left ∈ centralPositiveHalfStates w hw K half →
          ∀ right,
            right ∈ centralPositiveHalfStates w hw K half →
              endpoint.joint left right ≈
                centralNormalizedFixedMagneticReferenceGram
                  w hw K half referenceWeight left right)
    (hreference :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels K half →
          (0 : Q') ≤ referenceWeight channel)
    (hactive :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K half →
        ∀ channel,
          channel ∈
              (centralFixedMagneticIntertwinerChannels K half).filter
                (centralFixedMagneticActiveCore
                  w K half source) →
            Q'.abs
                (centralFixedMagneticIntertwinerWeight
                      w half channel +
                  (-referenceWeight channel)) ≤
              Q'.mkPos 1 16 (by decide) *
                centralFixedMagneticIntertwinerWeight
                  w half channel) :
    FixedMagneticCoreTailEndpointRealization
      hw K half endpoint where
  referenceWeight := referenceWeight
  joint_identification := hjoint
  coreTail :=
    activeCoreTailEighthData
      hw K half referenceWeight hreference hactive

end YMGap.Continuum.BF4FixedMagneticActiveRowCore

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FixedMagneticActiveRowCore.source_amplitude_eqv_zero_of_tail
#print axioms YMGap.Continuum.BF4FixedMagneticActiveRowCore.activeTail_weightedGram_eqv_zero
#print axioms YMGap.Continuum.BF4FixedMagneticActiveRowCore.activeTail_weightedGramRowMass_eqv_zero
#print axioms YMGap.Continuum.BF4FixedMagneticActiveRowCore.activeCoreTailEighthData
#print axioms YMGap.Continuum.BF4FixedMagneticActiveRowCore.activeCoreEndpointRealization
