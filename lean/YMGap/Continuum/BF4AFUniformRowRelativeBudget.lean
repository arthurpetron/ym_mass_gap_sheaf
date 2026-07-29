/-
# AF-uniform row-relative budgets for the physical BF4 endpoint comparison

The physical BF4 Perron transfer does not consume a plain unweighted
`epsilon / N` entry estimate.  Its exact hypothesis is relative to the
nonuniform physical row marginal:

    sum_y |J_phys(x,y) - J_M(x,y)| <= epsilon * pi_phys(x).

This module exposes the division-free estimates which are sufficient for
that hypothesis.  Both kernels are represented by raw numerators and
strictly positive partitions.  A normalized entry difference is controlled
by the cross numerator

    N_phys(x,y) Z_M - N_M(x,y) Z_phys.

There are two witness-bearing budget layers:

* `CentralPhysicalCrossRowBudget` accepts a direct cross-numerator bound;
* `CentralPhysicalNumeratorPartitionBudget` derives that bound from a raw
  numerator error, a partition error, and an endpoint-numerator ceiling.

In both cases the final, indispensable marginal payment is explicit:

    |positive carrier| * entryBudget(x)
      <= epsilon * pi_phys(x).

The last section packages one common `epsilon` over an arbitrary AF scale
index.  Its primary output is a
`CentralPhysicalSymmetricReferenceComparison` at every declared scale:
the Peter--Weyl endpoint may be a signed symmetric matrix-coefficient
projection, so no entrywise positivity or exact endpoint marginal is assumed.
The older joint-law comparison is available only through a separate optional
certificate.  This module does not assert that the analytic numerator,
partition, or marginal estimates hold on the physical trajectory.

## Honest scope

This file proves all normalization and finite-carrier bookkeeping needed
after the Peter--Weyl endpoint transform is available.  It does not construct
that transform and does not inhabit any AF-uniform physical estimate.

## Axiom gate

Finite list recursion and exact `Q'` algebra only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SymmetricReferenceOperatorComparison

namespace YMGap.Continuum.BF4AFUniformRowRelativeBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
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
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Constructive normalization algebra -/

/-- A division-free absolute numerator estimate controls division by a
strictly positive denominator:

`|num| <= budget * denominator` implies
`|num / denominator| <= budget`.
-/
theorem abs_divPos_le_of_abs_le_mul
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross :
      Q'.abs numerator ≤ budget * denominator) :
    Q'.abs
        (Q'.divPos numerator denominator hdenominator) ≤
      budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross :
        -(budget * denominator) ≤
          -(Q'.abs numerator) :=
      Q'.neg_le_neg hcross
    have hnegAbs :
        -(Q'.abs numerator) ≤ numerator := by
      have h :=
        Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv
          (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _
      (Q'.le_abs_self numerator) hcross

/-- Clearing the two positive partitions from a normalized entry difference
produces the usual cross numerator. -/
theorem normalized_entry_difference_eqv_cross_div
    (physicalNumerator endpointNumerator
      physicalPartition endpointPartition : Q')
    (hphysicalPartition :
      (0 : Q') < physicalPartition)
    (hendpointPartition :
      (0 : Q') < endpointPartition) :
    Q'.divPos physicalNumerator
          physicalPartition hphysicalPartition +
        (-Q'.divPos endpointNumerator
          endpointPartition hendpointPartition) ≈
      Q'.divPos
        (physicalNumerator * endpointPartition +
          (-(endpointNumerator * physicalPartition)))
        (physicalPartition * endpointPartition)
        (Q'.mul_pos
          hphysicalPartition hendpointPartition) := by
  apply Q'.mul_left_cancel_of_pos
    (Q'.mul_pos hphysicalPartition hendpointPartition)
  have hphysical :
      (physicalPartition * endpointPartition) *
          Q'.divPos physicalNumerator
            physicalPartition hphysicalPartition ≈
        physicalNumerator * endpointPartition := by
    refine Q'.eqv_trans _
      (endpointPartition *
        (Q'.divPos physicalNumerator
          physicalPartition hphysicalPartition *
            physicalPartition)) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _
      (endpointPartition * physicalNumerator) _
      (Q'.mul_eqv_congr_left endpointPartition _ _
        (Q'.divPos_mul_eqv
          physicalNumerator physicalPartition
          hphysicalPartition)) ?_
    exact Q'.mul_comm_eqv
      endpointPartition physicalNumerator
  have hendpoint :
      (physicalPartition * endpointPartition) *
          Q'.divPos endpointNumerator
            endpointPartition hendpointPartition ≈
        endpointNumerator * physicalPartition := by
    refine Q'.eqv_trans _
      (physicalPartition *
        (Q'.divPos endpointNumerator
          endpointPartition hendpointPartition *
            endpointPartition)) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _
      (physicalPartition * endpointNumerator) _
      (Q'.mul_eqv_congr_left physicalPartition _ _
        (Q'.divPos_mul_eqv
          endpointNumerator endpointPartition
          hendpointPartition)) ?_
    exact Q'.mul_comm_eqv
      physicalPartition endpointNumerator
  refine Q'.eqv_trans _
    ((physicalPartition * endpointPartition) *
        Q'.divPos physicalNumerator
          physicalPartition hphysicalPartition +
      (-((physicalPartition * endpointPartition) *
        Q'.divPos endpointNumerator
          endpointPartition hendpointPartition))) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((physicalPartition * endpointPartition) *
        Q'.divPos physicalNumerator
          physicalPartition hphysicalPartition +
        (physicalPartition * endpointPartition) *
          (-Q'.divPos endpointNumerator
            endpointPartition hendpointPartition)) _ ?_ ?_
    · exact Q'.mul_add_eqv _ _ _
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv
        (physicalPartition * endpointPartition)
        (Q'.divPos endpointNumerator
          endpointPartition hendpointPartition))
  refine Q'.eqv_trans _
    (physicalNumerator * endpointPartition +
      (-(endpointNumerator * physicalPartition))) _
    (Q'.add_eqv_congr' hphysical
      (Q'.neg_eqv_congr _ _ hendpoint)) ?_
  refine Q'.eqv_trans _
    (Q'.divPos
        (physicalNumerator * endpointPartition +
          (-(endpointNumerator * physicalPartition)))
        (physicalPartition * endpointPartition)
        (Q'.mul_pos
          hphysicalPartition hendpointPartition) *
      (physicalPartition * endpointPartition)) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.divPos_mul_eqv
        (physicalNumerator * endpointPartition +
          (-(endpointNumerator * physicalPartition)))
        (physicalPartition * endpointPartition)
        (Q'.mul_pos
          hphysicalPartition hendpointPartition))
  exact Q'.mul_comm_eqv
    (Q'.divPos
      (physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition)))
      (physicalPartition * endpointPartition)
      (Q'.mul_pos
        hphysicalPartition hendpointPartition))
    (physicalPartition * endpointPartition)

/-- The cross-numerator estimate immediately gives the normalized entry
estimate. -/
theorem normalized_entry_difference_abs_le_of_cross
    (physicalNumerator endpointNumerator
      physicalPartition endpointPartition entryBudget : Q')
    (hphysicalPartition :
      (0 : Q') < physicalPartition)
    (hendpointPartition :
      (0 : Q') < endpointPartition)
    (hcross :
      Q'.abs
          (physicalNumerator * endpointPartition +
            (-(endpointNumerator * physicalPartition))) ≤
        entryBudget *
          (physicalPartition * endpointPartition)) :
    Q'.abs
        (Q'.divPos physicalNumerator
            physicalPartition hphysicalPartition +
          (-Q'.divPos endpointNumerator
            endpointPartition hendpointPartition)) ≤
      entryBudget := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (abs_eqv_congr
        (normalized_entry_difference_eqv_cross_div
          physicalNumerator endpointNumerator
          physicalPartition endpointPartition
          hphysicalPartition hendpointPartition))) ?_
  exact abs_divPos_le_of_abs_le_mul
    (Q'.mul_pos
      hphysicalPartition hendpointPartition)
    hcross

/-! ## 2. Numerator and partition decomposition -/

/-- Algebraic decomposition of the cross numerator:

`P ZM - M ZP = (P-M) ZM + M (ZM-ZP)`.
-/
theorem cross_numerator_decomposition
    (physicalNumerator endpointNumerator
      physicalPartition endpointPartition : Q') :
    physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition)) ≈
      (physicalNumerator + (-endpointNumerator)) *
          endpointPartition +
        endpointNumerator *
          (endpointPartition + (-physicalPartition)) := by
  refine Q'.eqv_symm (Q'.eqv_trans _
    ((physicalNumerator * endpointPartition +
        (-endpointNumerator) * endpointPartition) +
      (endpointNumerator * endpointPartition +
        endpointNumerator * (-physicalPartition))) _ ?_ ?_)
  · exact Q'.add_eqv_congr'
      (Q'.add_mul_eqv
        physicalNumerator (-endpointNumerator)
        endpointPartition)
      (Q'.mul_add_eqv endpointNumerator
        endpointPartition (-physicalPartition))
  refine Q'.eqv_trans _
    ((physicalNumerator * endpointPartition +
        (-endpointNumerator) * endpointPartition) +
      (endpointNumerator * (-physicalPartition) +
        endpointNumerator * endpointPartition)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left
      (physicalNumerator * endpointPartition +
        (-endpointNumerator) * endpointPartition)
      _ _
      (Q'.add_comm_eqv
        (endpointNumerator * endpointPartition)
        (endpointNumerator * (-physicalPartition)))
  refine Q'.eqv_trans _
    ((physicalNumerator * endpointPartition +
        endpointNumerator * (-physicalPartition)) +
      ((-endpointNumerator) * endpointPartition +
        endpointNumerator * endpointPartition)) _ ?_ ?_
  · exact Q'.add_swap_inner
      (physicalNumerator * endpointPartition)
      ((-endpointNumerator) * endpointPartition)
      (endpointNumerator * (-physicalPartition))
      (endpointNumerator * endpointPartition)
  refine Q'.eqv_trans _
    ((physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition))) +
      ((-(endpointNumerator * endpointPartition)) +
        endpointNumerator * endpointPartition)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left
        (physicalNumerator * endpointPartition) _ _
        (Q'.mul_neg_eqv
          endpointNumerator physicalPartition))
      (Q'.add_eqv_congr_right
        ((-endpointNumerator) * endpointPartition)
        (-(endpointNumerator * endpointPartition))
        (endpointNumerator * endpointPartition)
        (Q'.neg_mul_eqv
          endpointNumerator endpointPartition))
  refine Q'.eqv_trans _
    ((physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition))) +
      0) _
    (Q'.add_eqv_congr_left
      (physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition)))
      _ _
      (Q'.neg_add_self_eqv
        (endpointNumerator * endpointPartition))) ?_
  exact Q'.eqv_of_eq
    (Q'.add_zero'
      (physicalNumerator * endpointPartition +
        (-(endpointNumerator * physicalPartition))))

/-- Separate numerator and partition errors control the cross numerator.
Endpoint nonnegativity removes an otherwise unnecessary absolute value from
the endpoint-numerator ceiling. -/
theorem cross_numerator_abs_le_of_numerator_partition
    (physicalNumerator endpointNumerator
      physicalPartition endpointPartition
      numeratorError partitionError endpointNumeratorCeiling : Q')
    (hendpointPartitionNonnegative :
      (0 : Q') ≤ endpointPartition)
    (hnumerator :
      Q'.abs
          (physicalNumerator + (-endpointNumerator)) ≤
        numeratorError)
    (hpartition :
      Q'.abs
          (physicalPartition + (-endpointPartition)) ≤
        partitionError)
    (hendpointNumeratorCeiling :
      Q'.abs endpointNumerator ≤
        endpointNumeratorCeiling) :
    Q'.abs
        (physicalNumerator * endpointPartition +
          (-(endpointNumerator * physicalPartition))) ≤
      numeratorError * endpointPartition +
        endpointNumeratorCeiling * partitionError := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (abs_eqv_congr
        (cross_numerator_decomposition
          physicalNumerator endpointNumerator
          physicalPartition endpointPartition))) ?_
  refine Q'.le_trans' _ _ _
    (abs_add_le
      ((physicalNumerator + (-endpointNumerator)) *
        endpointPartition)
      (endpointNumerator *
        (endpointPartition + (-physicalPartition)))) ?_
  apply Q'.add_le_add
  · refine Q'.le_trans' _ _ _
      (abs_mul_le
        (physicalNumerator + (-endpointNumerator))
        endpointPartition) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hnumerator
        (Q'.abs_nonneg endpointPartition)) ?_
    have habsPartitionEq :
        Q'.abs endpointPartition = endpointPartition := by
      unfold Q'.abs
      rw [if_pos hendpointPartitionNonnegative]
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left numeratorError _ _
        (Q'.eqv_of_eq habsPartitionEq))
  · refine Q'.le_trans' _ _ _
      (abs_mul_le endpointNumerator
        (endpointPartition + (-physicalPartition))) ?_
    have hreversePartition :
        Q'.abs
            (endpointPartition + (-physicalPartition)) ≤
          partitionError := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (abs_eqv_congr
            (Q'.eqv_trans _
              ((-physicalPartition) + endpointPartition) _
              (Q'.add_comm_eqv endpointPartition
                (-physicalPartition))
              (Q'.eqv_trans _
                ((-physicalPartition) +
                  (-(-endpointPartition))) _
                (Q'.add_eqv_congr_left
                  (-physicalPartition)
                  endpointPartition
                  (-(-endpointPartition))
                  (Q'.eqv_symm
                    (Q'.neg_neg_eqv
                      endpointPartition)))
                (Q'.eqv_symm
                  (Q'.neg_add_eqv
                    physicalPartition
                    (-endpointPartition))))))) ?_
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_neg'
            (physicalPartition + (-endpointPartition))))
        hpartition
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hreversePartition
        (Q'.abs_nonneg endpointNumerator)) ?_
    have hpartitionErrorNonnegative :
        (0 : Q') ≤ partitionError :=
      Q'.le_trans' _ _ _
        (Q'.abs_nonneg
          (physicalPartition + (-endpointPartition)))
        hpartition
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      hendpointNumeratorCeiling
      hpartitionErrorNonnegative

/-! ## 3. Signed symmetric raw endpoint data on the exact physical carrier -/

/-- Division by the exact unit partition changes no rational value. -/
theorem divPos_one_eqv (value : Q') :
    Q'.divPos value 1 (by decide) ≈ value := by
  exact Q'.eqv_trans _
    (Q'.divPos value 1 (by decide) * 1) _
    (Q'.eqv_symm
      (Q'.mul_one_eqv
        (Q'.divPos value 1 (by decide))))
    (Q'.divPos_mul_eqv value 1 (by decide))

/-- Pointwise equivalent finite joint matrices have equivalent finite
quadratic forms. -/
theorem finiteJointQuadratic_joint_eqv
    {State : Type}
    (states : List State)
    (observable : State → Q')
    (leftJoint rightJoint : State → State → Q')
    (hjoint :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          leftJoint left right ≈
            rightJoint left right) :
    finiteJointQuadratic states observable leftJoint ≈
      finiteJointQuadratic states observable rightJoint := by
  unfold finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left
    (observable left * observable right) _ _
    (hjoint left hleft right hright)

/-- A raw, partition-normalized symmetric endpoint operator on the exact
positive-row BF4 carrier.  This is the interface expected from the genuine
Peter--Weyl matrix-coefficient transform.

The numerator may have either sign.  Peter--Weyl coefficients are not
entrywise probability weights; the actual required output is a symmetric
positive-semidefinite operator with a physical-mean-zero Rayleigh bound.
Physical-minus-endpoint convergence belongs to the separate budget
structures below.
-/
structure CentralPhysicalRawMehlerEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  /-- Raw transformed endpoint numerator. -/
  numerator : EdgeLabelling → EdgeLabelling → Q'
  /-- Raw endpoint partition. -/
  partition : Q'
  partition_pos : (0 : Q') < partition
  numerator_symmetric :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      right ∈ centralPositiveHalfStates w hw K halfExtent →
        numerator left right ≈ numerator right left
  /-- Positive-semidefiniteness of the normalized signed endpoint matrix. -/
  normalized_quadratic_nonnegative :
    ∀ observable : EdgeLabelling → Q',
      (0 : Q') ≤
        finiteJointQuadratic
          (centralPositiveHalfStates
            w hw K halfExtent)
          observable
          (fun left right =>
            Q'.divPos
              (numerator left right)
              partition partition_pos)
  /-- Located rational Perron rate. -/
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  /-- Endpoint contraction on the exact physical mean-zero carrier. -/
  normalized_meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero
        w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates
                w hw K halfExtent)
              observable
              (fun left right =>
                Q'.divPos
                  (numerator left right)
                  partition partition_pos)) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

namespace CentralPhysicalRawMehlerEndpoint

/-- The normalized signed endpoint matrix.

The historical field name `joint` records the two-boundary source/target
indexing.  It does not assert entrywise nonnegativity or a probability
marginal; those are separate optional data in `JointLawCertificate`. -/
def joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    EdgeLabelling → EdgeLabelling → Q' :=
  fun left right =>
    Q'.divPos
      (endpoint.numerator left right)
      endpoint.partition endpoint.partition_pos

theorem joint_symmetric
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates
        w hw K halfExtent)
    (hright :
      right ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    endpoint.joint left right ≈
      endpoint.joint right left := by
  unfold joint Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (endpoint.numerator_symmetric
      left right hleft hright)

/-- The raw normalized endpoint supplies the natural symmetric PSD
common-carrier reference operator. -/
def toSymmetricReferenceOperator
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) :
    CentralSymmetricReferenceOperator
      w hw K halfExtent where
  matrix := endpoint.joint
  symmetric := by
    intro left right hleft hright
    exact endpoint.joint_symmetric
      hleft hright
  quadratic_nonnegative :=
    endpoint.normalized_quadratic_nonnegative
  rate := endpoint.rate
  rate_nonnegative := endpoint.rate_nonnegative
  meanZero_quadratic :=
    endpoint.normalized_meanZero_quadratic

/-- A genuine double-Haar Peter--Weyl projection, together with its PSD and
Rayleigh certificate, gives a raw endpoint with unit partition.

The projected matrix may be signed.  No entrywise positivity or marginal
claim is introduced by this adapter.
-/
def ofPeterWeylProjection
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent}
    (projection :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw)
    (spectral :
      CentralPositiveGaussianEndpointSpectralCertificate
        projection) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator := projection.projectedJoint
  partition := 1
  partition_pos := by decide
  numerator_symmetric :=
    projection.projectedJoint_symmetric
  normalized_quadratic_nonnegative := by
    intro observable
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    have hquadratic :
        finiteJointQuadratic states observable
            (fun left right =>
              Q'.divPos
                (projection.projectedJoint left right)
                1 (by decide)) ≈
          finiteJointQuadratic states observable
            projection.projectedJoint := by
      exact finiteJointQuadratic_joint_eqv
        states observable
        (fun left right =>
          Q'.divPos
            (projection.projectedJoint left right)
            1 (by decide))
        projection.projectedJoint
        (fun left _ right _ =>
          divPos_one_eqv
            (projection.projectedJoint left right))
    exact Q'.le_trans' _ _ _
      (spectral.quadratic_nonnegative observable)
      (Q'.ge_of_eqv hquadratic)
  rate := spectral.rate
  rate_nonnegative := spectral.rate_nonnegative
  normalized_meanZero_quadratic := by
    intro observable hmean
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    have hquadratic :
        finiteJointQuadratic states observable
            (fun left right =>
              Q'.divPos
                (projection.projectedJoint left right)
                1 (by decide)) ≈
          finiteJointQuadratic states observable
            projection.projectedJoint := by
      exact finiteJointQuadratic_joint_eqv
        states observable
        (fun left right =>
          Q'.divPos
            (projection.projectedJoint left right)
            1 (by decide))
        projection.projectedJoint
        (fun left _ right _ =>
          divPos_one_eqv
            (projection.projectedJoint left right))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (abs_eqv_congr hquadratic))
      (spectral.meanZero_quadratic
        observable hmean)

/-- Optional extra data upgrading the signed symmetric endpoint matrix to an
entrywise-positive joint law with the exact physical marginal.

This does not belong to the primary Peter--Weyl/Perron route.
-/
structure JointLawCertificate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent) : Type where
  entry_nonnegative :
    ∀ left,
      left ∈ centralPositiveHalfStates
        w hw K halfExtent →
      ∀ right,
        right ∈ centralPositiveHalfStates
          w hw K halfExtent →
        (0 : Q') ≤ endpoint.joint left right
  physical_rowMarginal :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        listQSum
            (endpoint.joint source)
            (centralPositiveHalfStates
              w hw K halfExtent) ≈
          centralPhysicalRowMarginal
            w hw K halfExtent source

end CentralPhysicalRawMehlerEndpoint

/-! ## 4. Direct cross-numerator row budget -/

/-- Direct division-free budget for the physical-minus-endpoint rows.

The entry budget is paid twice: first against the raw cross numerator, then
against the exact physical marginal after multiplying by the carrier size.
-/
structure CentralPhysicalCrossRowBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q') : Type where
  entryBudget : EdgeLabelling → Q'
  entryBudget_nonnegative :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        (0 : Q') ≤ entryBudget source
  cross_error :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
      ∀ target,
        target ∈ centralPositiveHalfStates
          w hw K halfExtent →
        Q'.abs
            (centralPhysicalReflectedKernel
                  w K halfExtent source target *
                endpoint.partition +
              (-(endpoint.numerator source target *
                slabParametricKPhysicalPartition
                  w K (centralExtent halfExtent)))) ≤
          entryBudget source *
            (slabParametricKPhysicalPartition
                w K (centralExtent halfExtent) *
              endpoint.partition)
  marginal_payment :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        Q'.ofNat
            (centralPositiveHalfStates
              w hw K halfExtent).length *
            entryBudget source ≤
          epsilon *
            centralPhysicalRowMarginal
              w hw K halfExtent source

namespace CentralPhysicalCrossRowBudget

/-- Every retained normalized entry obeys its source-dependent budget. -/
theorem normalized_entry_abs_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent}
    {epsilon : Q'}
    (budget :
      CentralPhysicalCrossRowBudget
        endpoint epsilon)
    {source target : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent)
    (htarget :
      target ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    Q'.abs
        (centralNormalizedPhysicalReflectedKernel
              w hw K halfExtent source target +
          (-endpoint.joint source target)) ≤
      budget.entryBudget source := by
  unfold centralNormalizedPhysicalReflectedKernel
    CentralPhysicalRawMehlerEndpoint.joint
  exact normalized_entry_difference_abs_le_of_cross
    (centralPhysicalReflectedKernel
      w K halfExtent source target)
    (endpoint.numerator source target)
    (slabParametricKPhysicalPartition
      w K (centralExtent halfExtent))
    endpoint.partition
    (budget.entryBudget source)
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent halfExtent))
    endpoint.partition_pos
    (budget.cross_error
      source hsource target htarget)

/-- The direct cross budget supplies exactly the row-relative hypothesis
consumed by the signed symmetric-reference comparison. -/
theorem row_relative_error
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent}
    {epsilon : Q'}
    (budget :
      CentralPhysicalCrossRowBudget
        endpoint epsilon)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralNormalizedPhysicalReflectedKernel
          w hw K halfExtent)
        endpoint.joint source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact
    finiteJointDifferenceAbsRowMass_le_of_entrywise_budget
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent)
      endpoint.joint
      budget.entryBudget
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      epsilon
      (budget.entryBudget_nonnegative
        source hsource)
      (fun target htarget =>
        budget.normalized_entry_abs_le
          hsource htarget)
      (budget.marginal_payment
        source hsource)

/-- Assemble the primary signed symmetric-reference comparison from raw
endpoint data and the division-free cross budget. -/
def toSymmetricReferenceComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (budget :
      CentralPhysicalCrossRowBudget
        endpoint epsilon) :
    CentralPhysicalSymmetricReferenceComparison
      w hw K halfExtent where
  reference := endpoint.toSymmetricReferenceOperator
  epsilon := epsilon
  epsilon_nonnegative := hepsilon
  row_relative_error := by
    intro source hsource
    exact budget.row_relative_error hsource

/-- Optional upgrade to the older entrywise joint-law interface.  The
primary symmetric-reference Perron consumer does not need this. -/
def toMehlerComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (jointLaw :
      CentralPhysicalRawMehlerEndpoint.JointLawCertificate
        endpoint)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (budget :
      CentralPhysicalCrossRowBudget
        endpoint epsilon) :
    CentralPhysicalMehlerComparison
      w hw K halfExtent :=
  let symmetricComparison :=
    budget.toSymmetricReferenceComparison
      endpoint epsilon hepsilon
  symmetricComparison.toPhysicalMehlerComparison
    { entry_nonnegative :=
        jointLaw.entry_nonnegative
      physical_rowMarginal :=
        jointLaw.physical_rowMarginal }

end CentralPhysicalCrossRowBudget

/-! ## 5. An explicit marginal-floor payment -/

/-- Witness-bearing lower envelope for the physical row marginal.

This isolates the precise additional information absent from an unweighted
`epsilon / N` estimate.  The source-dependent floor must sit below the
literal physical Choi marginal, and the complete carrier growth must already
fit below `epsilon` times that floor.
-/
structure CentralPhysicalMarginalFloorBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (epsilon : Q')
    (entryBudget : EdgeLabelling → Q') : Type where
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  marginalFloor : EdgeLabelling → Q'
  marginalFloor_nonnegative :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        (0 : Q') ≤ marginalFloor source
  marginalFloor_le_physical :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        marginalFloor source ≤
          centralPhysicalRowMarginal
            w hw K halfExtent source
  carrier_payment :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        Q'.ofNat
            (centralPositiveHalfStates
              w hw K halfExtent).length *
            entryBudget source ≤
          epsilon * marginalFloor source

namespace CentralPhysicalMarginalFloorBudget

/-- A physical marginal floor pays the exact carrier-weighted entry budget. -/
theorem marginal_payment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {epsilon : Q'}
    {entryBudget : EdgeLabelling → Q'}
    (budget :
      CentralPhysicalMarginalFloorBudget
        (w := w) (hw := hw)
        (K := K) (halfExtent := halfExtent)
        epsilon entryBudget)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    Q'.ofNat
        (centralPositiveHalfStates
          w hw K halfExtent).length *
        entryBudget source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact Q'.le_trans' _ _ _
    (budget.carrier_payment source hsource)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (budget.marginalFloor_le_physical
        source hsource)
      budget.epsilon_nonnegative)

end CentralPhysicalMarginalFloorBudget

/-! ## 6. Separated numerator / partition / marginal budget -/

/-- More analytic budget layer.  Instead of estimating the cross numerator
directly, it supplies:

* a physical-vs-endpoint numerator error;
* an endpoint numerator ceiling;
* a physical-vs-endpoint partition error;
* the algebraic payment of those errors into one normalized entry budget;
* the final physical-marginal payment.

All constants are data.  None is extracted from a propositional existence.
-/
structure CentralPhysicalNumeratorPartitionBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q') : Type where
  numeratorError : EdgeLabelling → Q'
  endpointNumeratorCeiling : EdgeLabelling → Q'
  partitionError : Q'
  entryBudget : EdgeLabelling → Q'
  numeratorError_nonnegative :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        (0 : Q') ≤ numeratorError source
  endpointNumeratorCeiling_nonnegative :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        (0 : Q') ≤ endpointNumeratorCeiling source
  partitionError_nonnegative :
    (0 : Q') ≤ partitionError
  entryBudget_nonnegative :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        (0 : Q') ≤ entryBudget source
  numerator_error :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
      ∀ target,
        target ∈ centralPositiveHalfStates
          w hw K halfExtent →
        Q'.abs
            (centralPhysicalReflectedKernel
                  w K halfExtent source target +
              (-endpoint.numerator source target)) ≤
          numeratorError source
  endpoint_numerator_ceiling :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
      ∀ target,
        target ∈ centralPositiveHalfStates
          w hw K halfExtent →
        Q'.abs
            (endpoint.numerator source target) ≤
          endpointNumeratorCeiling source
  partition_error :
    Q'.abs
        (slabParametricKPhysicalPartition
              w K (centralExtent halfExtent) +
          (-endpoint.partition)) ≤
      partitionError
  normalized_entry_payment :
    ∀ source,
      source ∈ centralPositiveHalfStates
        w hw K halfExtent →
        numeratorError source * endpoint.partition +
            endpointNumeratorCeiling source *
              partitionError ≤
          entryBudget source *
            (slabParametricKPhysicalPartition
                w K (centralExtent halfExtent) *
              endpoint.partition)
  /-- Explicit physical-marginal lower envelope and carrier payment. -/
  marginalBudget :
    CentralPhysicalMarginalFloorBudget
      (w := w) (hw := hw)
      (K := K) (halfExtent := halfExtent)
      epsilon entryBudget

namespace CentralPhysicalNumeratorPartitionBudget

/-- The separated analytic budgets imply the direct cross-numerator budget. -/
def toCrossRowBudget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (budget :
      CentralPhysicalNumeratorPartitionBudget
        endpoint epsilon) :
    CentralPhysicalCrossRowBudget endpoint epsilon where
  entryBudget := budget.entryBudget
  entryBudget_nonnegative :=
    budget.entryBudget_nonnegative
  cross_error := by
    intro source hsource target htarget
    refine Q'.le_trans' _ _ _
      (cross_numerator_abs_le_of_numerator_partition
        (centralPhysicalReflectedKernel
          w K halfExtent source target)
        (endpoint.numerator source target)
        (slabParametricKPhysicalPartition
          w K (centralExtent halfExtent))
        endpoint.partition
        (budget.numeratorError source)
        budget.partitionError
        (budget.endpointNumeratorCeiling source)
        (Q'.le_of_lt endpoint.partition_pos)
        (budget.numerator_error
          source hsource target htarget)
        budget.partition_error
        (budget.endpoint_numerator_ceiling
          source hsource target htarget)) ?_
    exact budget.normalized_entry_payment
      source hsource
  marginal_payment := by
    intro source hsource
    exact budget.marginalBudget.marginal_payment
      hsource

/-- The separated numerator/partition/marginal estimates supply the exact
row-relative hypothesis. -/
theorem row_relative_error
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {epsilon : Q'}
    (budget :
      CentralPhysicalNumeratorPartitionBudget
        endpoint epsilon)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          w hw K halfExtent)
        (centralNormalizedPhysicalReflectedKernel
          w hw K halfExtent)
        endpoint.joint source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  (budget.toCrossRowBudget
    endpoint epsilon).row_relative_error hsource

/-- Assemble the primary signed symmetric-reference comparison directly
from the separated analytic budgets. -/
def toSymmetricReferenceComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (budget :
      CentralPhysicalNumeratorPartitionBudget
        endpoint epsilon) :
    CentralPhysicalSymmetricReferenceComparison
      w hw K halfExtent :=
  (budget.toCrossRowBudget endpoint epsilon).toSymmetricReferenceComparison
    endpoint epsilon hepsilon

/-- Optional joint-law upgrade for the separated analytic budget. -/
def toMehlerComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    (jointLaw :
      CentralPhysicalRawMehlerEndpoint.JointLawCertificate
        endpoint)
    (epsilon : Q')
    (hepsilon : (0 : Q') ≤ epsilon)
    (budget :
      CentralPhysicalNumeratorPartitionBudget
        endpoint epsilon) :
    CentralPhysicalMehlerComparison
      w hw K halfExtent :=
  (budget.toCrossRowBudget endpoint epsilon).toMehlerComparison
    endpoint jointLaw epsilon hepsilon

end CentralPhysicalNumeratorPartitionBudget

/-! ## 7. One common row-relative budget along an AF scale family -/

/-- A common row-relative tolerance along an arbitrary indexed BF4 scale
family.  The supplied endpoint and cross budget may vary with scale; the
same rational `epsilon` must pay every row at every scale.

This is a trajectory consumer, not an inhabitant for the physical BF4
trajectory.
-/
structure CentralPhysicalAFUniformRowBudget
    {Scale : Type}
    (weight : Scale → Q')
    (weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale)
    (cutoff halfExtent : Scale → Nat) : Type where
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  endpoint :
    ∀ scale,
      CentralPhysicalRawMehlerEndpoint
        (weight scale)
        (weight_nonnegative scale)
        (cutoff scale)
        (halfExtent scale)
  crossBudget :
    ∀ scale,
      CentralPhysicalCrossRowBudget
        (endpoint scale) epsilon

namespace CentralPhysicalAFUniformRowBudget

/-- Every scale of a uniform family gives the exact signed symmetric
comparison consumed by the weighted Perron theorem, with the same error
tolerance. -/
def comparisonAt
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformRowBudget
        weight weight_nonnegative cutoff halfExtent)
    (scale : Scale) :
    CentralPhysicalSymmetricReferenceComparison
      (weight scale)
      (weight_nonnegative scale)
      (cutoff scale)
      (halfExtent scale) :=
  (family.crossBudget scale).toSymmetricReferenceComparison
    (family.endpoint scale)
    family.epsilon
    family.epsilon_nonnegative

/-- The common AF budget gives the physical row-relative estimate at every
declared scale. -/
theorem row_relative_error_at
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformRowBudget
        weight weight_nonnegative cutoff halfExtent)
    (scale : Scale)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        (weight scale)
        (weight_nonnegative scale)
        (cutoff scale)
        (halfExtent scale)) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale))
        (centralNormalizedPhysicalReflectedKernel
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale))
        (family.endpoint scale).joint source ≤
      family.epsilon *
        centralPhysicalRowMarginal
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale) source :=
  (family.crossBudget scale).row_relative_error
    hsource

/-- Once the scale-dependent endpoint rate plus the common AF row budget
fits below `1/4`, the exact nonlinear physical Markov quadratic has the
quarter contraction at that scale. -/
theorem physical_markov_quadratic_abs_le_quarter_at
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformRowBudget
        weight weight_nonnegative cutoff halfExtent)
    (scale : Scale)
    (hquarter :
      (family.endpoint scale).rate +
          family.epsilon ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (weight scale)
        (weight_nonnegative scale)
        (cutoff scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (weight scale)
            (weight_nonnegative scale)
            (cutoff scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale)
          observable observable := by
  exact
    CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le_quarter
      (family.comparisonAt scale) hquarter observable hmean

end CentralPhysicalAFUniformRowBudget

/-! ## 8. AF-uniform separated analytic budgets -/

/-- AF-uniform form of the separated numerator/partition/marginal budget.

The raw endpoint data and each analytic budget may vary with the scale
index, while the final row-relative `epsilon` is one common rational.
-/
structure CentralPhysicalAFUniformNumeratorPartitionBudget
    {Scale : Type}
    (weight : Scale → Q')
    (weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale)
    (cutoff halfExtent : Scale → Nat) : Type where
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  endpoint :
    ∀ scale,
      CentralPhysicalRawMehlerEndpoint
        (weight scale)
        (weight_nonnegative scale)
        (cutoff scale)
        (halfExtent scale)
  analyticBudget :
    ∀ scale,
      CentralPhysicalNumeratorPartitionBudget
        (endpoint scale) epsilon

namespace CentralPhysicalAFUniformNumeratorPartitionBudget

/-- Forgetting the separated estimates gives the common direct cross-row
budget family. -/
def toUniformRowBudget
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformNumeratorPartitionBudget
        weight weight_nonnegative cutoff halfExtent) :
    CentralPhysicalAFUniformRowBudget
      weight weight_nonnegative cutoff halfExtent where
  epsilon := family.epsilon
  epsilon_nonnegative := family.epsilon_nonnegative
  endpoint := family.endpoint
  crossBudget := fun scale =>
    (family.analyticBudget scale).toCrossRowBudget
      (family.endpoint scale) family.epsilon

/-- Every scale of the separated AF-uniform analytic family yields the exact
signed physical endpoint comparison. -/
def comparisonAt
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformNumeratorPartitionBudget
        weight weight_nonnegative cutoff halfExtent)
    (scale : Scale) :
    CentralPhysicalSymmetricReferenceComparison
      (weight scale)
      (weight_nonnegative scale)
      (cutoff scale)
      (halfExtent scale) :=
  family.toUniformRowBudget.comparisonAt scale

/-- The separated AF-uniform estimates prove the requested physical
row-relative bound at every scale. -/
theorem row_relative_error_at
    {Scale : Type}
    {weight : Scale → Q'}
    {weight_nonnegative :
      ∀ scale, (0 : Q') ≤ weight scale}
    {cutoff halfExtent : Scale → Nat}
    (family :
      CentralPhysicalAFUniformNumeratorPartitionBudget
        weight weight_nonnegative cutoff halfExtent)
    (scale : Scale)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        (weight scale)
        (weight_nonnegative scale)
        (cutoff scale)
        (halfExtent scale)) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale))
        (centralNormalizedPhysicalReflectedKernel
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale))
        (family.endpoint scale).joint source ≤
      family.epsilon *
        centralPhysicalRowMarginal
          (weight scale)
          (weight_nonnegative scale)
          (cutoff scale)
          (halfExtent scale) source :=
  family.toUniformRowBudget.row_relative_error_at
    scale hsource

end CentralPhysicalAFUniformNumeratorPartitionBudget

end YMGap.Continuum.BF4AFUniformRowRelativeBudget

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.abs_divPos_le_of_abs_le_mul
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.normalized_entry_difference_eqv_cross_div
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.normalized_entry_difference_abs_le_of_cross
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.cross_numerator_decomposition
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.cross_numerator_abs_le_of_numerator_partition
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.divPos_one_eqv
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.finiteJointQuadratic_joint_eqv
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalRawMehlerEndpoint.joint_symmetric
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalRawMehlerEndpoint.ofPeterWeylProjection
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalCrossRowBudget.normalized_entry_abs_le
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalCrossRowBudget.row_relative_error
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalCrossRowBudget.toSymmetricReferenceComparison
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalMarginalFloorBudget.marginal_payment
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalNumeratorPartitionBudget.row_relative_error
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalNumeratorPartitionBudget.toSymmetricReferenceComparison
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalAFUniformRowBudget.row_relative_error_at
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalAFUniformRowBudget.comparisonAt
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalAFUniformRowBudget.physical_markov_quadratic_abs_le_quarter_at
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalAFUniformNumeratorPartitionBudget.row_relative_error_at
#print axioms YMGap.Continuum.BF4AFUniformRowRelativeBudget.CentralPhysicalAFUniformNumeratorPartitionBudget.comparisonAt
