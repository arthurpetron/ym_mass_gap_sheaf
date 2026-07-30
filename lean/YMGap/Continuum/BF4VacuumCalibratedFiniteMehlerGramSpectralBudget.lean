/-
# Stationary-vacuum calibration of the finite BF4 Mehler Gram

The canonical positive Mehler Gram is normalized by its own vacuum
coefficient, so its vacuum--vacuum entry is one.  The physical reflected
kernel is instead a probability joint with stationary marginal `pi`.
`BF4CanonicalFiniteMehlerGramSpectralBudget` proves that the uncalibrated
quarter cost therefore forces the nonphysical condition `pi(0) > 1/2`.

This module removes that scalar obstruction constructively.  It multiplies
the Gram by the literal square `pi(0)^2`, so the vacuum entry agrees exactly
with the stationary rank-one joint `pi ⊗ pi`.  Square scaling preserves
symmetry, positive semidefiniteness, and the physical-mean-zero Rayleigh
bound.  The remaining quarter estimate is consequently a genuine
Yang--Mills entry/tail estimate, rather than a normalization mismatch.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive square scaling -/

/-- Scaling every entry of a finite joint pulls through its quadratic form. -/
theorem finiteJointQuadratic_scale_joint
    {State : Type}
    (states : List State)
    (observable : State → Q')
    (scale : Q')
    (joint : State → State → Q') :
    finiteJointQuadratic states observable
        (fun left right => scale * joint left right) ≈
      scale *
        finiteJointQuadratic states observable joint := by
  unfold finiteJointQuadratic
  have hinner :
      ∀ left,
        listQSum
            (fun right =>
              (observable left * observable right) *
                (scale * joint left right))
            states ≈
          scale *
            listQSum
              (fun right =>
                (observable left * observable right) *
                  joint left right)
              states := by
    intro left
    refine Q'.eqv_trans _ _ _
      (listQSum_congr (fun right => ?_) states)
      (listQSum_mul_left
        scale
        (fun right =>
          (observable left * observable right) *
            joint left right)
        states)
    exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (observable left * observable right)
            scale (joint left right)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            ((observable left * observable right) * scale)
            (scale * (observable left * observable right))
            (joint left right)
            (Q'.mul_comm_eqv
              (observable left * observable right)
              scale))
          (Q'.mul_assoc_eqv
            scale
            (observable left * observable right)
            (joint left right)))
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hinner states) ?_
  exact listQSum_mul_left
      scale
      (fun left =>
        listQSum
          (fun right =>
            (observable left * observable right) *
              joint left right)
          states)
      states

/-- Multiplying a raw endpoint numerator and its Rayleigh rate by a rational
square preserves every algebraic endpoint field. -/
def squareScaledRawMehlerEndpoint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (scale : Q') (_hscale : (0 : Q') ≤ scale)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator :=
    fun left right =>
      (scale * scale) * endpoint.numerator left right
  partition := endpoint.partition
  partition_pos := endpoint.partition_pos
  numerator_symmetric := by
    intro left right hleft hright
    exact Q'.mul_eqv_congr_left
      (scale * scale)
      (endpoint.numerator left right)
      (endpoint.numerator right left)
      (endpoint.numerator_symmetric
        left right hleft hright)
  normalized_quadratic_nonnegative := by
    intro observable
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let oldJoint := endpoint.joint
    let scaledJoint :=
      fun left right =>
        Q'.divPos
          ((scale * scale) *
            endpoint.numerator left right)
          endpoint.partition endpoint.partition_pos
    have hentry :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            scaledJoint left right ≈
              (scale * scale) * oldJoint left right := by
      intro left _ right _
      unfold scaledJoint oldJoint
        CentralPhysicalRawMehlerEndpoint.joint
        Q'.divPos
      exact Q'.mul_assoc_eqv
        (scale * scale)
        (endpoint.numerator left right)
        (Q'.recipPos
          endpoint.partition endpoint.partition_pos)
    have hquadratic :
        finiteJointQuadratic states observable scaledJoint ≈
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint := by
      exact Q'.eqv_trans _ _ _
        (finiteJointQuadratic_joint_eqv
          states observable scaledJoint
          (fun left right =>
            (scale * scale) * oldJoint left right)
          hentry)
        (finiteJointQuadratic_scale_joint
          states observable (scale * scale) oldJoint)
    have hproduct :
        (0 : Q') ≤
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint :=
      Q'.mul_nonneg _ _
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
          scale)
        (endpoint.normalized_quadratic_nonnegative
          observable)
    exact Q'.le_trans' _ _ _
      hproduct (Q'.ge_of_eqv hquadratic)
  rate := (scale * scale) * endpoint.rate
  rate_nonnegative :=
    Q'.mul_nonneg _ _
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        scale)
      endpoint.rate_nonnegative
  normalized_meanZero_quadratic := by
    intro observable hmean
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let oldJoint := endpoint.joint
    let scaledJoint :=
      fun left right =>
        Q'.divPos
          ((scale * scale) *
            endpoint.numerator left right)
          endpoint.partition endpoint.partition_pos
    have hsquare :
        (0 : Q') ≤ scale * scale :=
      YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        scale
    have hentry :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            scaledJoint left right ≈
              (scale * scale) * oldJoint left right := by
      intro left _ right _
      unfold scaledJoint oldJoint
        CentralPhysicalRawMehlerEndpoint.joint
        Q'.divPos
      exact Q'.mul_assoc_eqv
        (scale * scale)
        (endpoint.numerator left right)
        (Q'.recipPos
          endpoint.partition endpoint.partition_pos)
    have hquadratic :
        finiteJointQuadratic states observable scaledJoint ≈
          (scale * scale) *
            finiteJointQuadratic states observable oldJoint := by
      exact Q'.eqv_trans _ _ _
        (finiteJointQuadratic_joint_eqv
          states observable scaledJoint
          (fun left right =>
            (scale * scale) * oldJoint left right)
          hentry)
        (finiteJointQuadratic_scale_joint
          states observable (scale * scale) oldJoint)
    have habsFactor :
        Q'.abs
            ((scale * scale) *
              finiteJointQuadratic
                states observable oldJoint) ≤
          (scale * scale) *
            Q'.abs
              (finiteJointQuadratic
                states observable oldJoint) := by
      have hmul :=
        YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
          (scale * scale)
          (finiteJointQuadratic
            states observable oldJoint)
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
        hsquare] at hmul
      exact hmul
    have hold :=
      endpoint.normalized_meanZero_quadratic
        observable hmean
    have hscaled :
        (scale * scale) *
            Q'.abs
              (finiteJointQuadratic
                states observable oldJoint) ≤
          (scale * scale) *
            (endpoint.rate *
              centralPhysicalWeightedInner
                w hw K halfExtent
                observable observable) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hold hsquare
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr hquadratic))
        habsFactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (scale * scale)
              endpoint.rate
              (centralPhysicalWeightedInner
                w hw K halfExtent
                observable observable)))))

/-- The normalized joint of a square-scaled endpoint is the corresponding
square multiple of the original joint. -/
theorem squareScaledRawMehlerEndpoint_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (scale : Q') (hscale : (0 : Q') ≤ scale)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (left right : EdgeLabelling) :
    (squareScaledRawMehlerEndpoint
        scale hscale endpoint).joint left right ≈
      (scale * scale) * endpoint.joint left right := by
  unfold squareScaledRawMehlerEndpoint
    CentralPhysicalRawMehlerEndpoint.joint
    Q'.divPos
  exact Q'.mul_assoc_eqv
    (scale * scale)
    (endpoint.numerator left right)
    (Q'.recipPos
      endpoint.partition endpoint.partition_pos)

/-! ## 2. Exact physical repartitioning -/

/-- Rewrite a raw endpoint over the exact physical BF4 partition without
changing its normalized joint, PSD quadratic, or Rayleigh rate.

The new numerator is `Z_phys * endpoint.joint` and the new partition is
`Z_phys`.  This removes a purely scalar partition mismatch from the
separated numerator/partition comparison budget. -/
def physicalRepartitionRawMehlerEndpoint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator :=
    fun left right =>
      slabParametricKPhysicalPartition
          w K (centralExtent halfExtent) *
        endpoint.joint left right
  partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  partition_pos :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent)
  numerator_symmetric := by
    intro left right hleft hright
    exact Q'.mul_eqv_congr_left
      (slabParametricKPhysicalPartition
        w K (centralExtent halfExtent))
      (endpoint.joint left right)
      (endpoint.joint right left)
      (endpoint.joint_symmetric hleft hright)
  normalized_quadratic_nonnegative := by
    intro observable
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let repartitionedJoint :=
      fun left right =>
        Q'.divPos
          (slabParametricKPhysicalPartition
              w K (centralExtent halfExtent) *
            endpoint.joint left right)
          (slabParametricKPhysicalPartition
            w K (centralExtent halfExtent))
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent halfExtent))
    have hjoint :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            repartitionedJoint left right ≈
              endpoint.joint left right := by
      intro left _ right _
      unfold repartitionedJoint Q'.divPos
      let partition :=
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent)
      let reciprocal :=
        Q'.recipPos partition
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent halfExtent))
      let entry := endpoint.joint left right
      change (partition * entry) * reciprocal ≈ entry
      refine Q'.eqv_trans _
        (partition * (entry * reciprocal)) _ ?_ ?_
      · exact Q'.mul_assoc_eqv partition entry reciprocal
      refine Q'.eqv_trans _
        (partition * (reciprocal * entry)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left partition _ _
          (Q'.mul_comm_eqv entry reciprocal)
      refine Q'.eqv_trans _
        ((partition * reciprocal) * entry) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.mul_assoc_eqv partition reciprocal entry)
      refine Q'.eqv_trans _ ((1 : Q') * entry) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ entry
          (Q'.mul_recipPos_eqv partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent halfExtent)))
      · exact Q'.one_mul_eqv entry
    exact Q'.le_trans' _ _ _
      (endpoint.normalized_quadratic_nonnegative observable)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (finiteJointQuadratic_joint_eqv
            states observable
            repartitionedJoint endpoint.joint hjoint)))
  rate := endpoint.rate
  rate_nonnegative := endpoint.rate_nonnegative
  normalized_meanZero_quadratic := by
    intro observable hmean
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let repartitionedJoint :=
      fun left right =>
        Q'.divPos
          (slabParametricKPhysicalPartition
              w K (centralExtent halfExtent) *
            endpoint.joint left right)
          (slabParametricKPhysicalPartition
            w K (centralExtent halfExtent))
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent halfExtent))
    have hjoint :
        ∀ left, left ∈ states →
          ∀ right, right ∈ states →
            repartitionedJoint left right ≈
              endpoint.joint left right := by
      intro left _ right _
      unfold repartitionedJoint Q'.divPos
      let partition :=
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent)
      let reciprocal :=
        Q'.recipPos partition
          (slabParametricKPhysicalPartition_pos
            hw K (centralExtent halfExtent))
      let entry := endpoint.joint left right
      change (partition * entry) * reciprocal ≈ entry
      refine Q'.eqv_trans _
        (partition * (entry * reciprocal)) _ ?_ ?_
      · exact Q'.mul_assoc_eqv partition entry reciprocal
      refine Q'.eqv_trans _
        (partition * (reciprocal * entry)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left partition _ _
          (Q'.mul_comm_eqv entry reciprocal)
      refine Q'.eqv_trans _
        ((partition * reciprocal) * entry) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.mul_assoc_eqv partition reciprocal entry)
      refine Q'.eqv_trans _ ((1 : Q') * entry) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ entry
          (Q'.mul_recipPos_eqv partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent halfExtent)))
      · exact Q'.one_mul_eqv entry
    have hquadratic :
        finiteJointQuadratic
            states observable repartitionedJoint ≈
          finiteJointQuadratic
            states observable endpoint.joint :=
      finiteJointQuadratic_joint_eqv
        states observable
        repartitionedJoint endpoint.joint hjoint
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hquadratic))
      (endpoint.normalized_meanZero_quadratic
        observable hmean)

/-- Exact physical repartitioning leaves every normalized endpoint entry
unchanged. -/
theorem physicalRepartitionRawMehlerEndpoint_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (left right : EdgeLabelling) :
    (physicalRepartitionRawMehlerEndpoint endpoint).joint
        left right ≈
      endpoint.joint left right := by
  unfold physicalRepartitionRawMehlerEndpoint
    CentralPhysicalRawMehlerEndpoint.joint
    Q'.divPos
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let reciprocal :=
    Q'.recipPos partition
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent halfExtent))
  let entry := endpoint.joint left right
  change (partition * entry) * reciprocal ≈ entry
  refine Q'.eqv_trans _
    (partition * (entry * reciprocal)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv partition entry reciprocal
  refine Q'.eqv_trans _
    (partition * (reciprocal * entry)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left partition _ _
      (Q'.mul_comm_eqv entry reciprocal)
  refine Q'.eqv_trans _
    ((partition * reciprocal) * entry) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv partition reciprocal entry)
  refine Q'.eqv_trans _ ((1 : Q') * entry) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ entry
      (Q'.mul_recipPos_eqv partition
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent halfExtent)))
  · exact Q'.one_mul_eqv entry

/-- The separated comparison's partition error vanishes identically after
exact physical repartitioning. -/
theorem physicalRepartitionRawMehlerEndpoint_partitionError_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    exactPartitionError
        (physicalRepartitionRawMehlerEndpoint endpoint) ≈
      0 := by
  unfold exactPartitionError
    physicalRepartitionRawMehlerEndpoint
  exact Q'.eqv_trans _ _ _
    (Q'.abs_eqv_congr
      (Q'.add_neg_self_eqv
        (slabParametricKPhysicalPartition
          w K (centralExtent halfExtent))))
    (by decide)

/-- After exact physical repartitioning the separated cross majorant has no
partition contribution: it is precisely the raw numerator row error times
the common physical partition. -/
theorem physicalRepartitionRawMehlerEndpoint_crossMajorant
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    exactCrossMajorant
        (physicalRepartitionRawMehlerEndpoint endpoint)
        source ≈
      exactNumeratorError
          (physicalRepartitionRawMehlerEndpoint endpoint)
          source *
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent) := by
  unfold exactCrossMajorant
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (exactNumeratorError
          (physicalRepartitionRawMehlerEndpoint endpoint)
          source *
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent))
      _
      0
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (exactEndpointNumeratorCeiling
            (physicalRepartitionRawMehlerEndpoint endpoint)
            source)
          _
          0
          (physicalRepartitionRawMehlerEndpoint_partitionError_zero
            endpoint))
        (Q'.mul_zero_eqv _))) ?_
  exact Q'.eqv_of_eq
    (Q'.add_zero'
      (exactNumeratorError
          (physicalRepartitionRawMehlerEndpoint endpoint)
          source *
        slabParametricKPhysicalPartition
          w K (centralExtent halfExtent)))

/-- Local positive-division cancellation, kept here so the repartition
simplification does not depend on a separate spectral namespace. -/
private theorem divPos_eqv_of_eqv_mul_local
    {p q c : Q'} (hq : (0 : Q') < q)
    (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right p (c * q)
      (Q'.recipPos q hq) h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q
      (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

/-- The canonical normalized entry budget of a physically repartitioned
endpoint is exactly its raw numerator row error divided by the physical
partition.  Thus the comparison field no longer pays any independent
partition error. -/
theorem physicalRepartitionRawMehlerEndpoint_entryBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    exactEntryBudget
        (physicalRepartitionRawMehlerEndpoint endpoint)
        source ≈
      Q'.divPos
        (exactNumeratorError
          (physicalRepartitionRawMehlerEndpoint endpoint)
          source)
        (slabParametricKPhysicalPartition
          w K (centralExtent halfExtent))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent halfExtent)) := by
  let repartitioned :=
    physicalRepartitionRawMehlerEndpoint endpoint
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let error :=
    exactNumeratorError repartitioned source
  let quotient :=
    Q'.divPos error partition
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent halfExtent))
  have hmajorant :
      exactCrossMajorant repartitioned source ≈
        error * partition :=
    physicalRepartitionRawMehlerEndpoint_crossMajorant
      endpoint source
  have hquotient :
      quotient * partition ≈ error :=
    Q'.divPos_mul_eqv error partition
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent halfExtent))
  have hfactor :
      error * partition ≈
        quotient * (partition * partition) := by
    refine Q'.eqv_trans _ _ _
      ((Q'.eqv_symm
        (Q'.mul_eqv_congr_right
          (quotient * partition) error partition
          hquotient))) ?_
    exact Q'.mul_assoc_eqv quotient partition partition
  have hnumerator :
      exactCrossMajorant repartitioned source ≈
        quotient * (partition * partition) :=
    Q'.eqv_trans _ _ _ hmajorant hfactor
  unfold exactEntryBudget
  change
    Q'.divPos
        (exactCrossMajorant repartitioned source)
        (partition * partition)
        _ ≈ quotient
  exact divPos_eqv_of_eqv_mul_local
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent halfExtent))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent halfExtent)))
    hnumerator

/-- Canonical comparison tolerance after physical repartitioning, displayed
without the now-vanishing partition branch. -/
def physicalRepartitionNumeratorEpsilon
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  let repartitioned :=
    physicalRepartitionRawMehlerEndpoint endpoint
  let states := endpointStates repartitioned
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  Q'.divPos
    (Q'.ofNat states.length *
      listQSum
        (fun source =>
          Q'.divPos
            (exactNumeratorError repartitioned source)
            partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent halfExtent)))
        states)
    floorData.floor floorData.floor_pos

/-- The original fixed-carrier tolerance is exactly the numerator-only
tolerance after physical repartitioning. -/
theorem physicalRepartitionRawMehlerEndpoint_finiteEpsilon
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    exactFiniteEpsilon
        (physicalRepartitionRawMehlerEndpoint endpoint) ≈
      physicalRepartitionNumeratorEpsilon endpoint := by
  let repartitioned :=
    physicalRepartitionRawMehlerEndpoint endpoint
  let states := endpointStates repartitioned
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  have hsum :
      exactEntryBudgetSum repartitioned ≈
        listQSum
          (fun source =>
            Q'.divPos
              (exactNumeratorError repartitioned source)
              partition
              (slabParametricKPhysicalPartition_pos
                hw K (centralExtent halfExtent)))
          states := by
    unfold exactEntryBudgetSum
    exact listQSum_congr
      (fun source =>
        physicalRepartitionRawMehlerEndpoint_entryBudget
          endpoint source)
      states
  unfold exactFiniteEpsilon
    physicalRepartitionNumeratorEpsilon
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right
    (Q'.ofNat states.length *
      exactEntryBudgetSum repartitioned)
    (Q'.ofNat states.length *
      listQSum
        (fun source =>
          Q'.divPos
            (exactNumeratorError repartitioned source)
            partition
            (slabParametricKPhysicalPartition_pos
              hw K (centralExtent halfExtent)))
        states)
    (Q'.recipPos floorData.floor floorData.floor_pos)
    (Q'.mul_eqv_congr_left
      (Q'.ofNat states.length)
      _ _ hsum)

/-- Literal normalized physical-minus-endpoint mass in one retained row. -/
def physicalNormalizedJointRowError
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPositiveHalfStates w hw K halfExtent)
    (centralNormalizedPhysicalReflectedKernel
      w hw K halfExtent)
    endpoint.joint source

/-- The raw numerator-row error of a physically repartitioned endpoint is
bounded by the physical partition times the literal normalized row error. -/
theorem physicalRepartitionRawMehlerEndpoint_numeratorError_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    exactNumeratorError
        (physicalRepartitionRawMehlerEndpoint endpoint)
        source ≤
      slabParametricKPhysicalPartition
          w K (centralExtent halfExtent) *
        physicalNormalizedJointRowError endpoint source := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let physical :=
    centralNormalizedPhysicalReflectedKernel
      w hw K halfExtent
  have hpartitionPos :
      (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent)
  have hpartitionNonnegative :
      (0 : Q') ≤ partition :=
    Q'.le_of_lt hpartitionPos
  have hentry :
      ∀ target, target ∈ states →
        Q'.abs
            (centralPhysicalReflectedKernel
                  w K halfExtent source target +
              (-((physicalRepartitionRawMehlerEndpoint endpoint).numerator
                source target))) ≤
          partition *
            Q'.abs
              (physical source target +
                (-endpoint.joint source target)) := by
    intro target _
    let physicalEntry := physical source target
    let endpointEntry := endpoint.joint source target
    have hphysicalRaw :
        centralPhysicalReflectedKernel
            w K halfExtent source target ≈
          partition * physicalEntry := by
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv partition physicalEntry)
          (Q'.divPos_mul_eqv
            (centralPhysicalReflectedKernel
              w K halfExtent source target)
            partition hpartitionPos))
    change
      Q'.abs
          (centralPhysicalReflectedKernel
                w K halfExtent source target +
            (-(partition * endpointEntry))) ≤
        partition *
          Q'.abs
            (physicalEntry + (-endpointEntry))
    have hdifference :
        centralPhysicalReflectedKernel
              w K halfExtent source target +
            (-(partition * endpointEntry)) ≈
          partition * physicalEntry +
            (-(partition * endpointEntry)) :=
      Q'.add_eqv_congr_right _ _ _
        hphysicalRaw
    have hcommon :=
      abs_common_mul_sub_le
        partition physicalEntry endpointEntry
        (Q'.abs
          (physicalEntry + (-endpointEntry)))
        (Q'.le_refl' _)
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      hpartitionNonnegative] at hcommon
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hdifference))
      hcommon
  unfold exactNumeratorError
    physicalNormalizedJointRowError
    finiteJointDifferenceAbsRowMass
    endpointStates
  exact Q'.le_trans' _ _ _
    (listQSum_mono _ _ states hentry)
    (Q'.le_of_eqv
      (listQSum_mul_left
        partition
        (fun target =>
          Q'.abs
            (physical source target +
              (-endpoint.joint source target)))
        states))

/-- Once the common physical partition is cancelled, each canonical entry
budget is bounded directly by the normalized row error. -/
theorem physicalRepartitionRawMehlerEndpoint_entryBudget_le_rowError
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    exactEntryBudget
        (physicalRepartitionRawMehlerEndpoint endpoint)
        source ≤
      physicalNormalizedJointRowError endpoint source := by
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent halfExtent)
  let numeratorError :=
    exactNumeratorError
      (physicalRepartitionRawMehlerEndpoint endpoint)
      source
  let rowError :=
    physicalNormalizedJointRowError endpoint source
  have hpartitionPos :
      (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent)
  have hnumerator :
      numeratorError ≤ partition * rowError :=
    physicalRepartitionRawMehlerEndpoint_numeratorError_le
      endpoint source
  have hquotient :
      Q'.divPos numeratorError partition hpartitionPos ≤
        rowError := by
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _
      hnumerator
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv partition rowError))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (physicalRepartitionRawMehlerEndpoint_entryBudget
        endpoint source))
    hquotient

/-- Normalized-row majorant for the exact finite comparison tolerance. -/
def physicalNormalizedJointFiniteEpsilon
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  Q'.divPos
    (Q'.ofNat states.length *
      listQSum
        (physicalNormalizedJointRowError endpoint)
        states)
    floorData.floor floorData.floor_pos

/-- Division-free payment criterion for the normalized comparison eighth.
This is the exact aggregate all-label estimate that the grouped
Feynman--Kac/Mehler entry bound must discharge. -/
theorem physicalNormalizedJointFiniteEpsilon_le_eighth_of_cross
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (hcross :
      let states :=
        centralPositiveHalfStates w hw K halfExtent
      let floorData :=
        centralPositivePhysicalMarginalFloorData
          w hw K halfExtent
      Q'.ofNat states.length *
          listQSum
            (physicalNormalizedJointRowError endpoint)
            states ≤
        Q'.mkPos 1 8 (by decide) * floorData.floor) :
    physicalNormalizedJointFiniteEpsilon endpoint ≤
      Q'.mkPos 1 8 (by decide) := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  unfold physicalNormalizedJointFiniteEpsilon
  exact Q'.divPos_le_of_le_mul _ _ _
    hcross

/-- The exact canonical tolerance of a physically repartitioned endpoint is
bounded by the explicit normalized-row majorant. -/
theorem physicalRepartitionRawMehlerEndpoint_finiteEpsilon_le_normalized
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    exactFiniteEpsilon
        (physicalRepartitionRawMehlerEndpoint endpoint) ≤
      physicalNormalizedJointFiniteEpsilon endpoint := by
  let repartitioned :=
    physicalRepartitionRawMehlerEndpoint endpoint
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let floorData :=
    centralPositivePhysicalMarginalFloorData
      w hw K halfExtent
  have hsum :
      exactEntryBudgetSum repartitioned ≤
        listQSum
          (physicalNormalizedJointRowError endpoint)
          states := by
    unfold exactEntryBudgetSum endpointStates
    exact listQSum_mono _ _ states
      (fun source _ =>
        physicalRepartitionRawMehlerEndpoint_entryBudget_le_rowError
          endpoint source)
  have hnumerator :
      Q'.ofNat states.length *
          exactEntryBudgetSum repartitioned ≤
        Q'.ofNat states.length *
          listQSum
            (physicalNormalizedJointRowError endpoint)
            states :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hsum (Q'.ofNat_nonneg _)
  unfold exactFiniteEpsilon
    physicalNormalizedJointFiniteEpsilon
    Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    hnumerator
    (Q'.le_of_lt
      (Q'.recipPos_pos
        floorData.floor floorData.floor_pos))

/-! ## 3. Exact row-relative comparison without carrier overpayment -/

/-- Literal normalized physical-minus-endpoint row mass divided by the
physical stationary row marginal.  The zero branch lies outside the retained
positive-row carrier. -/
def physicalNormalizedJointRowRatio
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) : Q' :=
  if hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source
  then
    Q'.divPos
      (physicalNormalizedJointRowError endpoint source)
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      hpositive
  else 0

theorem physicalNormalizedJointRowError_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      physicalNormalizedJointRowError endpoint source := by
  unfold physicalNormalizedJointRowError
    finiteJointDifferenceAbsRowMass
  exact listQSum_nonnegative_on _ _
    (fun target _ => Q'.abs_nonneg _)

theorem physicalNormalizedJointRowRatio_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      physicalNormalizedJointRowRatio endpoint source := by
  unfold physicalNormalizedJointRowRatio
  split
  next hpositive =>
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (physicalNormalizedJointRowError_nonnegative
        endpoint source)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ hpositive))
  next _ =>
    exact Q'.le_refl' 0

/-- Constructive maximum of the exact physical-relative error over the
retained carrier.  This is the sharp finite Schur perturbation scalar; it
introduces neither carrier cardinality nor an inverse minimum marginal. -/
def physicalNormalizedJointMaxRowRatio
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Q' :=
  listQMaxZero
    (physicalNormalizedJointRowRatio endpoint)
    (centralPositiveHalfStates w hw K halfExtent)

theorem physicalNormalizedJointMaxRowRatio_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    (0 : Q') ≤
      physicalNormalizedJointMaxRowRatio endpoint := by
  unfold physicalNormalizedJointMaxRowRatio
  exact listQMaxZero_nonnegative _
    (physicalNormalizedJointRowRatio_nonnegative endpoint)
    (centralPositiveHalfStates w hw K halfExtent)

theorem listQMaxZero_le_of_on_mem
    {State : Type}
    (value : State → Q')
    (states : List State)
    (bound : Q')
    (hbound : (0 : Q') ≤ bound)
    (hvalue :
      ∀ state, state ∈ states →
        value state ≤ bound) :
    listQMaxZero value states ≤ bound := by
  induction states with
  | nil =>
      exact hbound
  | cons head tail inductionHypothesis =>
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ bound).mpr
        ⟨hvalue head (List.mem_cons_self),
          inductionHypothesis
            (fun state hstate =>
              hvalue state
                (List.mem_cons_of_mem head hstate))⟩

/-- A literal row-relative estimate bounds the executable maximum by the
same epsilon. -/
theorem physicalNormalizedJointMaxRowRatio_le_of_row_relative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (hrow :
      ∀ source,
        source ∈
            centralPositiveHalfStates
              w hw K halfExtent →
          physicalNormalizedJointRowError endpoint source ≤
            epsilon *
              centralPhysicalRowMarginal
                w hw K halfExtent source) :
    physicalNormalizedJointMaxRowRatio endpoint ≤
      epsilon := by
  unfold physicalNormalizedJointMaxRowRatio
  apply listQMaxZero_le_of_on_mem _ _ epsilon hepsilon
  intro source hsource
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  unfold physicalNormalizedJointRowRatio
  rw [dif_pos hpositive]
  exact Q'.divPos_le_of_le_mul _ _ _
    (hrow source hsource)

/-- Every retained normalized physical-minus-endpoint row is paid exactly by
the finite maximum times its own physical marginal. -/
theorem physicalNormalizedJointRowError_le_max_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates
          w hw K halfExtent) :
    physicalNormalizedJointRowError endpoint source ≤
      physicalNormalizedJointMaxRowRatio endpoint *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  have hratio :
      physicalNormalizedJointRowRatio endpoint source ≤
        physicalNormalizedJointMaxRowRatio endpoint := by
    exact le_listQMaxZero_of_mem
      (physicalNormalizedJointRowRatio endpoint)
      (centralPositiveHalfStates
        w hw K halfExtent)
      hsource
  unfold physicalNormalizedJointRowRatio at hratio
  rw [dif_pos hpositive] at hratio
  have hscaled :
      Q'.divPos
          (physicalNormalizedJointRowError endpoint source)
          (centralPhysicalRowMarginal
            w hw K halfExtent source)
          hpositive *
          centralPhysicalRowMarginal
            w hw K halfExtent source ≤
        physicalNormalizedJointMaxRowRatio endpoint *
          centralPhysicalRowMarginal
            w hw K halfExtent source :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hratio (Q'.le_of_lt hpositive)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (physicalNormalizedJointRowError endpoint source)
        (centralPhysicalRowMarginal
          w hw K halfExtent source)
        hpositive))
    hscaled

/-- Exact finite symmetric-reference comparison for any raw endpoint.  Its
epsilon is the literal maximum row-relative error, so this is the direct
weighted Schur certificate required by the physical Perron theorem. -/
def exactPhysicalNormalizedJointReferenceComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralPhysicalSymmetricReferenceComparison
      w hw K halfExtent where
  reference :=
    endpoint.toSymmetricReferenceOperator
  epsilon :=
    physicalNormalizedJointMaxRowRatio endpoint
  epsilon_nonnegative :=
    physicalNormalizedJointMaxRowRatio_nonnegative endpoint
  row_relative_error := by
    intro source hsource
    exact
      physicalNormalizedJointRowError_le_max_mul_marginal
        endpoint hsource

/-! ## 4. Physical stationary-vacuum calibration -/

/-- Square-calibrated positive Gram before the harmless exact physical
repartitioning. -/
def vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  squareScaledRawMehlerEndpoint
    pi0
    (centralPhysicalRowMarginal_nonnegative
      hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
    (exactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)

/-- Calibrate the exact positive Gram by the physical stationary-vacuum
amplitude `pi0²`. -/
def vacuumCalibratedExactCenteredMehlerGramRawEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent :=
  physicalRepartitionRawMehlerEndpoint
    (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)

/-- Vacuum calibration exactly matches the stationary rank-one vacuum
coefficient and hence removes the normalization fence. -/
theorem vacuumCalibratedExactCenteredMehlerGramRawEndpoint_vacuum
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).joint
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≈
      pi0 * pi0 := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hrepartition :=
    physicalRepartitionRawMehlerEndpoint_joint
      (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hscale :=
    squareScaledRawMehlerEndpoint_joint
      pi0
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
      (exactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  refine Q'.eqv_trans _ _ _ hrepartition ?_
  refine Q'.eqv_trans _ _ _ hscale ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (pi0 * pi0)
      ((exactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder).joint
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)
      1
      (normalizedBF4MehlerGramJoint_vacuum
        diagonalOrder crossOrder))
    (Q'.mul_one_eqv (pi0 * pi0))

/-- Stationary-vacuum calibration cannot increase the certified centered
Rayleigh rate, since every physical row marginal is at most one. -/
theorem vacuumCalibratedExactCenteredMehlerGramRawEndpoint_rate_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder).rate ≤
      exactCenteredMehlerGramRate
        w hw K halfExtent diagonalOrder crossOrder := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  let rate :=
    exactCenteredMehlerGramRate
      w hw K halfExtent diagonalOrder crossOrder
  have hvacuumMember :
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ∈
        centralPositiveHalfStates
          w hw K halfExtent :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent
  have hpi0nonnegative :
      (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hpi0le : pi0 ≤ (1 : Q') :=
    centralPhysicalRowMarginal_le_one_on_carrier
      hvacuumMember
  have hsquare :
      pi0 * pi0 ≤ (1 : Q') * 1 :=
    Q'.mul_le_mul_of_nonneg
      hpi0le hpi0le (by decide) hpi0nonnegative
  have hscaled :
      (pi0 * pi0) * rate ≤
        ((1 : Q') * 1) * rate :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hsquare
      (exactCenteredMehlerGramRate_nonnegative
        w hw K halfExtent diagonalOrder crossOrder)
  change (pi0 * pi0) * rate ≤ rate
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          ((1 : Q') * 1) 1 rate
          (Q'.mul_one_eqv 1))
        (Q'.one_mul_eqv rate)))

/-! ## 4. Matched physical AF coordinates -/

/-- The calibrated endpoint on the exact matched BF4 carrier at one scale. -/
def matchedVacuumCalibratedMehlerGramRawEndpointAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalRawMehlerEndpoint
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  vacuumCalibratedExactCenteredMehlerGramRawEndpoint
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (diagonalOrder scale)
    (crossOrder scale)

/-- The direct normalized-row comparison majorant at one matched scale. -/
def matchedVacuumCalibratedNormalizedComparisonAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  physicalNormalizedJointFiniteEpsilon
    (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (diagonalOrder scale)
      (crossOrder scale))

/-- Sharp row-relative comparison scalar on the exact matched carrier.  This
is the maximum of the literal normalized row errors divided by their own
physical marginals. -/
def matchedVacuumCalibratedSharpComparisonAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  physicalNormalizedJointMaxRowRatio
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)

/-- The calibrated endpoint and its exact row-relative maximum assemble a
signed symmetric-reference comparison at every matched finite scale. -/
def matchedVacuumCalibratedSharpReferenceComparisonAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalSymmetricReferenceComparison
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  exactPhysicalNormalizedJointReferenceComparison
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)

theorem matchedVacuumCalibratedSharpReferenceComparisonAt_rate
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    (matchedVacuumCalibratedSharpReferenceComparisonAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).reference.rate =
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).rate :=
  rfl

theorem matchedVacuumCalibratedSharpReferenceComparisonAt_epsilon
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    (matchedVacuumCalibratedSharpReferenceComparisonAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).epsilon =
      matchedVacuumCalibratedSharpComparisonAt
        family coupling halfExtent
        diagonalOrder crossOrder scale :=
  rfl

/-- At matched coordinates the exact separated tolerance is bounded by the
literal normalized physical-minus-calibrated row majorant. -/
theorem matchedVacuumCalibratedMehlerGram_finiteEpsilon_le_normalized
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    exactFiniteEpsilon
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale) ≤
      matchedVacuumCalibratedNormalizedComparisonAt
        family coupling halfExtent
        diagonalOrder crossOrder scale := by
  exact
    physicalRepartitionRawMehlerEndpoint_finiteEpsilon_le_normalized
      (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (crossOrder scale))

/-- The exact finite comparison cost after removing the scalar vacuum
normalization obstruction. -/
def matchedVacuumCalibratedMehlerGramQuarterCostAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  let endpoint :=
    matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale
  endpoint.rate + exactFiniteEpsilon endpoint

theorem matchedVacuumCalibratedMehlerGramQuarterCostAt_nonnegative
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    (0 : Q') ≤
      matchedVacuumCalibratedMehlerGramQuarterCostAt
        family coupling halfExtent
        diagonalOrder crossOrder scale := by
  unfold matchedVacuumCalibratedMehlerGramQuarterCostAt
  exact Q'.zero_le_add _ _
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale).rate_nonnegative
    (exactFiniteEpsilon_nonnegative
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale))

/-- The calibrated endpoint rate is the old exact centered rate multiplied
by the physical vacuum marginal square. -/
theorem matchedVacuumCalibratedMehlerGramRate_eqv
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).rate ≈
      (pi0 * pi0) *
        exactCenteredMehlerGramRate
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          (diagonalOrder scale)
          (crossOrder scale) := by
  unfold matchedVacuumCalibratedMehlerGramRawEndpointAt
    vacuumCalibratedExactCenteredMehlerGramRawEndpoint
    vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
    physicalRepartitionRawMehlerEndpoint
    squareScaledRawMehlerEndpoint
  exact Q'.eqv_refl _

/-- A quarter estimate for the calibrated exact cost gives the desired
physical mean-zero Markov contraction at that matched scale. -/
theorem matchedVacuumCalibratedMehlerGram_physical_quarter_at
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat)
    (hquarter :
      matchedVacuumCalibratedMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact
    exactFinite_physical_markov_quadratic_abs_le_quarter
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale)
      hquarter observable hmean

/-! ## 5. The corrected spacing-uniform analytic interface -/

/-- The two spacing-uniform eighth fields in their operator-sharp form.
The first controls the calibrated reference rate.  The second controls the
literal maximum row-relative physical-minus-reference error.  Together they
feed the signed symmetric-reference Perron consumer directly, without
carrier cardinality or minimum-marginal losses. -/
structure MatchedVacuumCalibratedSharpEighthBounds
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_eighth :
    ∀ scale,
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale).rate ≤
        Q'.mkPos 1 8 (by decide)
  comparison_eighth :
    ∀ scale,
      matchedVacuumCalibratedSharpComparisonAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 8 (by decide)

/-- Pointwise analytic form of the sharp comparison eighth.  This displays
the exact Yang--Mills kernel estimate to be proved for every retained row,
before the finite maximum is taken. -/
structure MatchedVacuumCalibratedRowwiseEighthEstimates
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_eighth :
    ∀ scale,
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale).rate ≤
        Q'.mkPos 1 8 (by decide)
  comparison_row_eighth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        physicalNormalizedJointRowError
            (matchedVacuumCalibratedMehlerGramRawEndpointAt
              family coupling halfExtent
              diagonalOrder crossOrder scale)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) source

namespace MatchedVacuumCalibratedRowwiseEighthEstimates

/-- The literal all-row Yang--Mills estimate computes the sharp comparison
maximum and therefore inhabits both operator-sharp eighth fields. -/
def toSharpEighthBounds
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (estimates :
      MatchedVacuumCalibratedRowwiseEighthEstimates
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedVacuumCalibratedSharpEighthBounds
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := estimates.coupling_pos
  coupling_le_window := estimates.coupling_le_window
  spectral_eighth := estimates.spectral_eighth
  comparison_eighth := by
    intro scale
    exact
      physicalNormalizedJointMaxRowRatio_le_of_row_relative
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)
        (Q'.mkPos 1 8 (by decide))
        (by decide)
        (estimates.comparison_row_eighth scale)

end MatchedVacuumCalibratedRowwiseEighthEstimates

namespace MatchedVacuumCalibratedSharpEighthBounds

/-- The two sharp eighth fields give the exact physical mean-zero quarter
contraction uniformly along the matched spacing trajectory. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (bounds :
      MatchedVacuumCalibratedSharpEighthBounds
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  let comparison :=
    matchedVacuumCalibratedSharpReferenceComparisonAt
      family coupling halfExtent
      diagonalOrder crossOrder scale
  have hquarter :
      comparison.reference.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide) := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add
        (bounds.spectral_eighth scale)
        (bounds.comparison_eighth scale)) ?_
    decide
  exact
    CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le_quarter
      comparison hquarter observable hmean

end MatchedVacuumCalibratedSharpEighthBounds

/-- The two genuinely analytic estimates remaining after stationary-vacuum
calibration.  The coupling window is tied to the same physical
`CubicMarginLaw` and `PhysicalSpacingEnvelope`; the two eighth-budgets are
stated on the literal matched carrier and exact finite tolerance. -/
structure MatchedVacuumCalibratedQuarterBudget
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_eighth :
    ∀ scale,
      (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale).rate ≤
        Q'.mkPos 1 8 (by decide)
  comparison_eighth :
    ∀ scale,
      exactFiniteEpsilon
          (matchedVacuumCalibratedMehlerGramRawEndpointAt
            family coupling halfExtent
            diagonalOrder crossOrder scale) ≤
        Q'.mkPos 1 8 (by decide)

/-- Sharpened analytic input for the two eighth fields.  The spectral scalar
is displayed before definitional endpoint packaging, and the comparison
scalar is the literal normalized physical-minus-calibrated row majorant.
Unlike the older separated budget, neither field contains an artificial
partition mismatch. -/
structure MatchedVacuumCalibratedNormalizedEighthBounds
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  centered_spectral_eighth :
    ∀ scale,
      let pi0 :=
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
      (pi0 * pi0) *
          exactCenteredMehlerGramRate
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            (diagonalOrder scale)
            (crossOrder scale) ≤
        Q'.mkPos 1 8 (by decide)
  normalized_comparison_cross_eighth :
    ∀ scale,
      let w :=
        matchedAllSpinWeight family coupling scale
      let hw :=
        matchedAllSpinWeight_nonnegative
          family coupling scale
      let K :=
        matchedAllSpinCutoff family coupling scale
      let half := halfExtent scale
      let states :=
        centralPositiveHalfStates w hw K half
      let floorData :=
        centralPositivePhysicalMarginalFloorData
          w hw K half
      let endpoint :=
        vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
          w hw K half
          (diagonalOrder scale) (crossOrder scale)
      Q'.ofNat states.length *
          listQSum
            (physicalNormalizedJointRowError endpoint)
            states ≤
        Q'.mkPos 1 8 (by decide) * floorData.floor

namespace MatchedVacuumCalibratedNormalizedEighthBounds

/-- The sharpened normalized estimates precisely inhabit the two original
spacing-uniform eighth fields. -/
def toQuarterBudget
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (bounds :
      MatchedVacuumCalibratedNormalizedEighthBounds
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedVacuumCalibratedQuarterBudget
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := bounds.coupling_pos
  coupling_le_window := bounds.coupling_le_window
  spectral_eighth := by
    intro scale
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (matchedVacuumCalibratedMehlerGramRate_eqv
          family coupling halfExtent
          diagonalOrder crossOrder scale))
      (bounds.centered_spectral_eighth scale)
  comparison_eighth := by
    intro scale
    exact Q'.le_trans' _ _ _
      (matchedVacuumCalibratedMehlerGram_finiteEpsilon_le_normalized
        family coupling halfExtent
        diagonalOrder crossOrder scale)
      (physicalNormalizedJointFiniteEpsilon_le_eighth_of_cross
        (vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          (diagonalOrder scale)
          (crossOrder scale))
        (bounds.normalized_comparison_cross_eighth scale))

end MatchedVacuumCalibratedNormalizedEighthBounds

namespace MatchedVacuumCalibratedQuarterBudget

/-- The two spacing-uniform eighth estimates add to the exact quarter
estimate at every scale. -/
theorem quarterCostAt_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (budget :
      MatchedVacuumCalibratedQuarterBudget
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    ∀ scale,
      matchedVacuumCalibratedMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide) := by
  intro scale
  unfold matchedVacuumCalibratedMehlerGramQuarterCostAt
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add
      (budget.spectral_eighth scale)
      (budget.comparison_eighth scale))
    (Q'.le_of_eqv (by decide))

/-- The calibrated budget supplies physical quarter contraction uniformly
on the complete matched AF trajectory. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (budget :
      MatchedVacuumCalibratedQuarterBudget
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact matchedVacuumCalibratedMehlerGram_physical_quarter_at
    family coupling halfExtent diagonalOrder crossOrder
    scale (budget.quarterCostAt_le scale)
    observable hmean

end MatchedVacuumCalibratedQuarterBudget

end YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.finiteJointQuadratic_scale_joint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.squareScaledRawMehlerEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.squareScaledRawMehlerEndpoint_joint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_joint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_partitionError_zero
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_crossMajorant
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_entryBudget
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionNumeratorEpsilon
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_finiteEpsilon
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointRowError
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_numeratorError_le
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_entryBudget_le_rowError
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointFiniteEpsilon
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointFiniteEpsilon_le_eighth_of_cross
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalRepartitionRawMehlerEndpoint_finiteEpsilon_le_normalized
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointRowRatio_nonnegative
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointMaxRowRatio_nonnegative
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.listQMaxZero_le_of_on_mem
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointMaxRowRatio_le_of_row_relative
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.physicalNormalizedJointRowError_le_max_mul_marginal
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.exactPhysicalNormalizedJointReferenceComparison
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumSquareScaledExactCenteredMehlerGramRawEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint_vacuum
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.vacuumCalibratedExactCenteredMehlerGramRawEndpoint_rate_le
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramRawEndpointAt
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramQuarterCostAt_nonnegative
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGramRate_eqv
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGram_finiteEpsilon_le_normalized
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedSharpReferenceComparisonAt
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedRowwiseEighthEstimates.toSharpEighthBounds
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedSharpEighthBounds.physical_quarter_uniform
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedNormalizedEighthBounds.toQuarterBudget
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.matchedVacuumCalibratedMehlerGram_physical_quarter_at
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedQuarterBudget.quarterCostAt_le
#print axioms YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget.MatchedVacuumCalibratedQuarterBudget.physical_quarter_uniform
