/-
# Physical BF4 specialization of same-carrier row CP domination

This module specializes `BF4SameCarrierRowCPDomination` to the literal
finite reflected SU(2) BF4 Choi law.

For every retained source, the physical boundary-channel Gram row has exact
mass

    Z_phys * pi(source).

Consequently a channelwise relative comparison on the same boundary carrier
gives, after exact common-partition normalization,

    sum_target |J_phys(source,target) - J_ref(source,target)|
      <= epsilon * pi(source).

This is the operator-sharp normalization required by the calibrated eighth
program.  No carrier-cardinality or minimum-marginal factor occurs.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4SameCarrierRowCPDomination
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

namespace YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SameCarrierRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ =>
      Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp,
            Bool.false_eq_true, if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (hzero head List.mem_cons_self hp)
                  (Q'.eqv_refl _))
                (Q'.eqv_of_eq
                  (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))

/-- Filtering zero-marginal targets does not change one retained physical
normalized row. -/
theorem centralNormalizedPositiveRow_eqv_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    listQSum
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source)
        (centralPositiveHalfStates
          w hw K half) ≈
      centralPhysicalRowMarginal
        w hw K half source := by
  have hsourceRaw :=
    (mem_centralPositiveHalfStates_iff.mp hsource).1
  unfold centralPositiveHalfStates
    centralPhysicalRowMarginal
  apply listQSum_filter_eq_of_zero_local
  intro target htarget hfalse
  exact
    centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
      hsourceRaw htarget
      (by
        simpa only [decide_eq_false_iff_not] using hfalse)

/-- On a retained source row, summing the unnormalized physical weighted
Gram over retained targets gives exactly `Z_phys * pi(source)`. -/
theorem centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    listQSum
        (fun target =>
          weightedGram
            (centralBoundaryChannels K half)
            (centralBoundaryWeight w K half)
            (centralHalfAmplitude w K half)
            source target)
        (centralPositiveHalfStates
          w hw K half) ≈
      slabParametricKPhysicalPartition
          w K (centralExtent half) *
        centralPhysicalRowMarginal
          w hw K half source := by
  let states :=
    centralPositiveHalfStates w hw K half
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let reciprocal :=
    Q'.recipPos partition
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
  let physicalRaw :=
    fun target =>
      centralPhysicalReflectedKernel
        w K half source target
  let physicalNormalized :=
    fun target =>
      centralNormalizedPhysicalReflectedKernel
        w hw K half source target
  have hsourceRaw :=
    (mem_centralPositiveHalfStates_iff.mp hsource).1
  have hgram :
      listQSum
          (fun target =>
            weightedGram
              (centralBoundaryChannels K half)
              (centralBoundaryWeight w K half)
              (centralHalfAmplitude w K half)
              source target)
          states ≈
        listQSum physicalRaw states := by
    apply listQSum_congr_on
    intro target htarget
    have htargetRaw :=
      (mem_centralPositiveHalfStates_iff.mp
        htarget).1
    exact Q'.eqv_symm
      (centralPhysicalReflectedKernel_eq_weightedGram
        w hsourceRaw htargetRaw)
  have hentry :
      ∀ target,
        physicalRaw target ≈
          partition * physicalNormalized target := by
    intro target
    unfold physicalRaw physicalNormalized
      centralNormalizedPhysicalReflectedKernel
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          partition
          (Q'.divPos
            (centralPhysicalReflectedKernel
              w K half source target)
            partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent half))))
        (Q'.divPos_mul_eqv
          (centralPhysicalReflectedKernel
            w K half source target)
          partition
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent half))))
  have hraw :
      listQSum physicalRaw states ≈
        partition *
          listQSum physicalNormalized states := by
    exact Q'.eqv_trans _ _ _
      (listQSum_congr hentry states)
      (listQSum_mul_left
        partition physicalNormalized states)
  exact Q'.eqv_trans _ _ _ hgram
    (Q'.eqv_trans _ _ _ hraw
      (Q'.mul_eqv_congr_left partition _ _
        (centralNormalizedPositiveRow_eqv_marginal
          hsource)))

/-- A same-boundary-carrier BF4 reference joint, normalized by the exact
physical partition. -/
def centralNormalizedBoundaryReferenceGram
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (referenceWeight : EdgeLabelling → Q')
    (left right : EdgeLabelling) : Q' :=
  normalizedWeightedGramJoint
    (centralBoundaryChannels K half)
    referenceWeight
    (centralHalfAmplitude w K half)
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))
    left right

/-- **Physical BF4 same-carrier row CP domination.**

A relative estimate on every retained boundary-channel integrand proves the
literal normalized all-target row estimate against the physical marginal. -/
theorem centralNormalizedBoundaryReferenceGram_row_error_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (referenceWeight : EdgeLabelling → Q')
    (epsilon : Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half)
    (hintegrand :
      ∀ target,
        target ∈
            centralPositiveHalfStates
              w hw K half →
          ∀ boundary,
            boundary ∈
                centralBoundaryChannels K half →
              Q'.abs
                  (centralBoundaryWeight w K half boundary *
                        (centralHalfAmplitude
                            w K half source boundary *
                          centralHalfAmplitude
                            w K half target boundary) +
                    (-(referenceWeight boundary *
                        (centralHalfAmplitude
                            w K half source boundary *
                          centralHalfAmplitude
                            w K half target boundary)))) ≤
                epsilon *
                  (centralBoundaryWeight w K half boundary *
                    (centralHalfAmplitude
                        w K half source boundary *
                      centralHalfAmplitude
                        w K half target boundary))) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K half)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half)
        (centralNormalizedBoundaryReferenceGram
          w hw K half referenceWeight)
        source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K half source := by
  let states :=
    centralPositiveHalfStates w hw K half
  let physicalReference :=
    normalizedWeightedGramJoint
      (centralBoundaryChannels K half)
      (centralBoundaryWeight w K half)
      (centralHalfAmplitude w K half)
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
  have hphysical :
      finiteJointDifferenceAbsRowMass
          states
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedBoundaryReferenceGram
            w hw K half referenceWeight)
          source ≈
        finiteJointDifferenceAbsRowMass
          states
          physicalReference
          (centralNormalizedBoundaryReferenceGram
            w hw K half referenceWeight)
          source := by
    unfold finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_right
    unfold physicalReference
      normalizedWeightedGramJoint
      Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalReflectedKernel_eq_weightedGram
        w
        (mem_centralPositiveHalfStates_iff.mp hsource).1
        (mem_centralPositiveHalfStates_iff.mp
          htarget).1)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hphysical)
    (normalizedWeightedGram_row_error_le_of_integrand_relative
      states
      (centralBoundaryChannels K half)
      (centralBoundaryWeight w K half)
      referenceWeight
      (centralHalfAmplitude w K half)
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      epsilon
      (centralPhysicalRowMarginal
        w hw K half source)
      source
      (centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
        hsource)
      hintegrand)

end YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination.centralNormalizedPositiveRow_eqv_marginal
#print axioms YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination.centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
#print axioms YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination.centralNormalizedBoundaryReferenceGram_row_error_le
