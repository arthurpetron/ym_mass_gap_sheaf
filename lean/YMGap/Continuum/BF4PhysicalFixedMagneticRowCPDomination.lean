/-
# Physical BF4 row domination on the fixed-magnetic carrier

The physical BF4 Choi law is exactly a weighted Gram after retaining:

* every fixed-face boundary label;
* every accepted fixed-link intertwiner; and
* every Peter--Weyl magnetic matrix index.

On this enlarged carrier every half-amplitude is nonnegative.  Consequently
a relative estimate on the physical and reference channel weights alone
implies the complete normalized row-relative estimate

    sum_y |J_phys(x,y) - J_ref(x,y)| <= epsilon * pi(x).

This is the all-label CP-order bridge needed by the second calibrated eighth.
It loses neither carrier cardinality nor a minimum marginal.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination
import YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier

namespace YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination
open YMGap.Continuum.BF4SameCarrierRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem slabFaceFactorOn_nonnegative_all
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (physical : EdgeLabelling) :
    ∀ ids : List Nat,
      (0 : Q') ≤ slabFaceFactorOn w K physical ids
  | [] => Q'.zero_le_one
  | id :: tail => by
      unfold slabFaceFactorOn eliminateLinks
      apply Q'.mul_nonneg
      · by_cases hspin : physical id < K + 1
        · rw [coeffAt_heatKernelPacket hspin]
          exact coeffW_nonneg hw _
        · have hlarge : K < physical id := by omega
          rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
          exact Q'.le_refl' 0
      · exact slabFaceFactorOn_nonnegative_all
          hw K physical tail

/-- Every physical lower-half BF4 amplitude is nonnegative.  The proof uses
the literal heat-packet coefficients and link multiplicities, including the
zero-extension branch above the cutoff. -/
theorem centralHalfAmplitude_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (state boundary : EdgeLabelling) :
    (0 : Q') ≤
      centralHalfAmplitude
        w K half state boundary := by
  unfold centralHalfAmplitude centralLowerFactor
  exact Q'.mul_nonneg _ _
    (slabFaceFactorOn_nonnegative_all
      hw K
      (assembleReflectedSlabLabelling
        half state boundary zeroEdgeLabelling)
      (centralLowerFaceIds half))
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)

/-- The magnetically enlarged physical Gram has the exact retained row mass
`Z_phys * pi(source)`. -/
theorem centralFixedMagneticPhysicalGram_positiveRow_eqv_partition_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    listQSum
        (fun target =>
          weightedGram
            (centralFixedMagneticIntertwinerChannels K half)
            (centralFixedMagneticIntertwinerWeight w half)
            (centralFixedMagneticIntertwinerHalfAmplitude
              w K half)
            source target)
        (centralPositiveHalfStates
          w hw K half) ≈
      slabParametricKPhysicalPartition
          w K (centralExtent half) *
        centralPhysicalRowMarginal
          w hw K half source := by
  let states :=
    centralPositiveHalfStates w hw K half
  have henlarged :
      listQSum
          (fun target =>
            weightedGram
              (centralFixedMagneticIntertwinerChannels K half)
              (centralFixedMagneticIntertwinerWeight w half)
              (centralFixedMagneticIntertwinerHalfAmplitude
                w K half)
              source target)
          states ≈
        listQSum
          (fun target =>
            weightedGram
              (centralBoundaryChannels K half)
              (centralBoundaryWeight w K half)
              (centralHalfAmplitude w K half)
              source target)
          states := by
    apply listQSum_congr_on
    intro target _htarget
    change
      centralFixedMagneticIntertwinerChoiEntry
          w K half source target ≈
        weightedGram
          (centralBoundaryChannels K half)
          (centralBoundaryWeight w K half)
          (centralHalfAmplitude w K half)
          source target
    exact centralFixedMagneticIntertwinerChoiEntry_eq
      w K half source target
  exact Q'.eqv_trans _ _ _
    henlarged
    (centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
      hsource)

/-- A fixed-magnetic common-carrier reference joint, normalized by the exact
physical slab partition. -/
def centralNormalizedFixedMagneticReferenceGram
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (left right : EdgeLabelling) : Q' :=
  normalizedWeightedGramJoint
    (centralFixedMagneticIntertwinerChannels K half)
    referenceWeight
    (centralFixedMagneticIntertwinerHalfAmplitude
      w K half)
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))
    left right

/-- The literal physical normalized Choi row agrees with the same-carrier
normalization using the fixed-magnetic physical weight. -/
theorem centralNormalizedPhysical_eqv_fixedMagneticGram
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half left right ≈
      normalizedWeightedGramJoint
        (centralFixedMagneticIntertwinerChannels K half)
        (centralFixedMagneticIntertwinerWeight w half)
        (centralFixedMagneticIntertwinerHalfAmplitude
          w K half)
        (slabParametricKPhysicalPartition
          w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half))
        left right := by
  unfold centralNormalizedPhysicalReflectedKernel
    normalizedWeightedGramJoint Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralPhysicalReflectedKernel_eq_fixedMagneticChoi
      w
      (mem_centralPositiveHalfStates_iff.mp hleft).1
      (mem_centralPositiveHalfStates_iff.mp hright).1)

/-- **Fixed-magnetic BF4 CP-order row theorem.**

It is enough to prove one relative scalar estimate for each retained enlarged
channel.  Nonnegativity of all physical half-amplitudes supplies the
source/target integrand estimate, and exact physical normalization supplies
the marginal on the right. -/
theorem centralNormalizedFixedMagneticReferenceGram_row_error_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    (epsilon : Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half)
    (hweight :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels
              K half →
          Q'.abs
              (centralFixedMagneticIntertwinerWeight
                    w half channel +
                (-referenceWeight channel)) ≤
            epsilon *
              centralFixedMagneticIntertwinerWeight
                w half channel) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedFixedMagneticReferenceGram
          w hw K half referenceWeight)
        source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K half source := by
  let states :=
    centralPositiveHalfStates w hw K half
  let channels :=
    centralFixedMagneticIntertwinerChannels K half
  let physicalReference :=
    normalizedWeightedGramJoint
      channels
      (centralFixedMagneticIntertwinerWeight w half)
      (centralFixedMagneticIntertwinerHalfAmplitude
        w K half)
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
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
          physicalReference
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half referenceWeight)
          source := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_right
    exact centralNormalizedPhysical_eqv_fixedMagneticGram
      hsource htarget
  have hintegrand :
      ∀ target, target ∈ states →
        ∀ channel, channel ∈ channels →
          Q'.abs
              (centralFixedMagneticIntertwinerWeight
                    w half channel *
                    (centralFixedMagneticIntertwinerHalfAmplitude
                        w K half source channel *
                      centralFixedMagneticIntertwinerHalfAmplitude
                        w K half target channel) +
                (-(referenceWeight channel *
                    (centralFixedMagneticIntertwinerHalfAmplitude
                        w K half source channel *
                      centralFixedMagneticIntertwinerHalfAmplitude
                        w K half target channel)))) ≤
            epsilon *
              (centralFixedMagneticIntertwinerWeight
                  w half channel *
                (centralFixedMagneticIntertwinerHalfAmplitude
                    w K half source channel *
                  centralFixedMagneticIntertwinerHalfAmplitude
                    w K half target channel)) := by
    exact
      weightedGram_integrand_relative_of_weight_relative
        states channels
        (centralFixedMagneticIntertwinerWeight w half)
        referenceWeight
        (centralFixedMagneticIntertwinerHalfAmplitude
          w K half)
        epsilon
        (fun state _hstate channel _hchannel => by
          unfold centralFixedMagneticIntertwinerHalfAmplitude
          exact centralHalfAmplitude_nonnegative
            hw K half state channel.1)
        hweight
        source hsource
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hphysical)
    (normalizedWeightedGram_row_error_le_of_integrand_relative
      states channels
      (centralFixedMagneticIntertwinerWeight w half)
      referenceWeight
      (centralFixedMagneticIntertwinerHalfAmplitude
        w K half)
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      epsilon
      (centralPhysicalRowMarginal
        w hw K half source)
      source
      (centralFixedMagneticPhysicalGram_positiveRow_eqv_partition_mul_marginal
        hsource)
      hintegrand)

/-- The concrete `[7/8,9/8]` Yang--Mills/Mehler weight window proves the
literal second calibrated eighth on every retained physical row. -/
theorem centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (referenceWeight :
      CentralFixedMagneticIntertwinerChannel → Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half)
    (hlower :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels
              K half →
          Q'.mkPos 7 8 (by decide) *
              centralFixedMagneticIntertwinerWeight
                w half channel ≤
            referenceWeight channel)
    (hupper :
      ∀ channel,
        channel ∈
            centralFixedMagneticIntertwinerChannels
              K half →
          referenceWeight channel ≤
            Q'.mkPos 9 8 (by decide) *
              centralFixedMagneticIntertwinerWeight
                w half channel) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedFixedMagneticReferenceGram
          w hw K half referenceWeight)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  apply centralNormalizedFixedMagneticReferenceGram_row_error_le
    referenceWeight
    (Q'.mkPos 1 8 (by decide))
    hsource
  intro channel hchannel
  exact weightRelativeEighth_of_sevenNineWindow
    (centralFixedMagneticIntertwinerWeight
      w half channel)
    (referenceWeight channel)
    (hlower channel hchannel)
    (hupper channel hchannel)

end YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination.centralHalfAmplitude_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination.centralFixedMagneticPhysicalGram_positiveRow_eqv_partition_mul_marginal
#print axioms YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination.centralNormalizedPhysical_eqv_fixedMagneticGram
#print axioms YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination.centralNormalizedFixedMagneticReferenceGram_row_error_le
#print axioms YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination.centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth
