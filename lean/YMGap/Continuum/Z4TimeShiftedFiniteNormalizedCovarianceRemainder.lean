/-
# Exact finite normalized covariance remainder for affine time translation

The affine time-shift transport is an exact weight-preserving bijection from
the source compatible gas onto its embedded image in the enlarged target
box.  It is not a bijection onto the full target gas.  This file puts those
two facts into one exact normalized identity.

For every finite cylinder, the full target numerator and partition are the
corresponding source quantities plus literal boundary-cell sums.  Both
boundary sums are nonnegative.  After normalization, the target-minus-source
probability is exactly the boundary cross-determinant divided by the product
of the two positive partition functions.  Consequently naive exact finite
volume covariance holds if and only if that boundary determinant vanishes.

No limiting argument, measured constant, reflection contraction, Hilbert
completion, or state-invariance hypothesis occurs here.
-/

import YMGap.Continuum.Z4TimeShiftedTargetCylinderStability

namespace YMGap.Continuum.Z4TimeShiftedFiniteNormalizedCovarianceRemainder

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem addMul_sub_mulAdd_eqv_cross_local
    (sourceNumerator boundaryNumerator sourcePartition boundaryPartition : Q') :
    (sourceNumerator + boundaryNumerator) * sourcePartition -
        sourceNumerator * (sourcePartition + boundaryPartition) ≈
      boundaryNumerator * sourcePartition -
        sourceNumerator * boundaryPartition := by
  let sourceCell := sourceNumerator * sourcePartition
  let boundaryEventCell := boundaryNumerator * sourcePartition
  let boundaryPartitionCell := sourceNumerator * boundaryPartition
  have hexpandLeft :
      (sourceNumerator + boundaryNumerator) * sourcePartition ≈
        sourceCell + boundaryEventCell := by
    exact Q'.add_mul_eqv
      sourceNumerator boundaryNumerator sourcePartition
  have hexpandRight :
      sourceNumerator * (sourcePartition + boundaryPartition) ≈
        sourceCell + boundaryPartitionCell := by
    exact Q'.mul_add_eqv
      sourceNumerator sourcePartition boundaryPartition
  have hnegExpand :
      -(sourceNumerator * (sourcePartition + boundaryPartition)) ≈
        (-sourceCell) + (-boundaryPartitionCell) := by
    exact Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hexpandRight)
      (Q'.neg_add_eqv sourceCell boundaryPartitionCell)
  have hexpand :
      (sourceNumerator + boundaryNumerator) * sourcePartition -
          sourceNumerator * (sourcePartition + boundaryPartition) ≈
        (sourceCell + boundaryEventCell) +
          ((-sourceCell) + (-boundaryPartitionCell)) := by
    exact Q'.add_eqv_congr' hexpandLeft hnegExpand
  have hswap :
      (sourceCell + boundaryEventCell) +
          ((-sourceCell) + (-boundaryPartitionCell)) ≈
        (sourceCell + (-sourceCell)) +
          (boundaryEventCell + (-boundaryPartitionCell)) :=
    Q'.add_swap_inner sourceCell boundaryEventCell
      (-sourceCell) (-boundaryPartitionCell)
  have hcancel :
      (sourceCell + (-sourceCell)) +
          (boundaryEventCell + (-boundaryPartitionCell)) ≈
        (0 : Q') +
          (boundaryEventCell + (-boundaryPartitionCell)) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv sourceCell)
  exact Q'.eqv_trans _ _ _ hexpand
    (Q'.eqv_trans _ _ _ hswap
      (Q'.eqv_trans _ _ _ hcancel
        (Q'.eqv_of_eq
          (Q'.zero_add'
            (boundaryEventCell + (-boundaryPartitionCell))))))

/-! ## 1. Generic exact normalization algebra -/

/-- The difference of two positive-denominator quotients is exactly their
cross-determinant divided by the product denominator. -/
theorem divPos_sub_eqv_crossDifference
    (targetNumerator targetPartition sourceNumerator sourcePartition : Q')
    (htarget : (0 : Q') < targetPartition)
    (hsource : (0 : Q') < sourcePartition) :
    Q'.divPos targetNumerator targetPartition htarget -
        Q'.divPos sourceNumerator sourcePartition hsource ≈
      Q'.divPos
        (targetNumerator * sourcePartition -
          sourceNumerator * targetPartition)
        (targetPartition * sourcePartition)
        (Q'.mul_pos htarget hsource) := by
  let targetRatio :=
    Q'.divPos targetNumerator targetPartition htarget
  let sourceRatio :=
    Q'.divPos sourceNumerator sourcePartition hsource
  have htargetCancel :
      (targetRatio * targetPartition) * sourcePartition ≈
        targetNumerator * sourcePartition := by
    exact Q'.mul_eqv_congr_right _ _ sourcePartition
      (Q'.divPos_mul_eqv
        targetNumerator targetPartition htarget)
  have hsourceCancel :
      (sourceRatio * sourcePartition) * targetPartition ≈
        sourceNumerator * targetPartition := by
    exact Q'.mul_eqv_congr_right _ _ targetPartition
      (Q'.divPos_mul_eqv
        sourceNumerator sourcePartition hsource)
  have hcancelled :
      (targetRatio * targetPartition) * sourcePartition -
          (sourceRatio * sourcePartition) * targetPartition ≈
        targetNumerator * sourcePartition -
          sourceNumerator * targetPartition :=
    sub_eqv_both_local htargetCancel hsourceCancel
  have hreorder :
      (targetRatio - sourceRatio) *
          (targetPartition * sourcePartition) ≈
        (targetRatio * targetPartition) * sourcePartition -
          (sourceRatio * sourcePartition) * targetPartition := by
    change
      (targetRatio + (-sourceRatio)) *
          (targetPartition * sourcePartition) ≈
        (targetRatio * targetPartition) * sourcePartition +
          (-((sourceRatio * sourcePartition) * targetPartition))
    ring_qeqv
  have hcross :
      targetNumerator * sourcePartition -
          sourceNumerator * targetPartition ≈
        (targetRatio - sourceRatio) *
          (targetPartition * sourcePartition) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancelled)
      (Q'.eqv_symm hreorder)
  exact Q'.eqv_symm
    (divPos_eqv_of_eqv_mul_local
      (Q'.mul_pos htarget hsource) hcross)

/-! ## 2. Literal nonnegative boundary cells -/

theorem couplingParametricKTimeShiftBoundaryTargetPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) :
    (0 : Q') ≤ couplingParametricKTimeShiftBoundaryTargetPartition
      coupling cutoff shift base := by
  unfold couplingParametricKTimeShiftBoundaryTargetPartition
  exact listQSum_nonnegative_generic _
    (fun family =>
      couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) family) _

theorem couplingParametricKTimeShiftBoundaryTargetEventNumerator_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤ couplingParametricKTimeShiftBoundaryTargetEventNumerator
      coupling cutoff shift base event := by
  unfold couplingParametricKTimeShiftBoundaryTargetEventNumerator
  exact listQSum_nonnegative_generic _
    (fun family =>
      couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) family) _

/-! ## 3. Source plus boundary decompositions -/

/-- The full enlarged-box partition is exactly the source partition plus the
nonnegative mass of target families outside the embedded translated cell. -/
theorem couplingParametricKTimeShiftFullPartition_eqv_source_add_boundary
    (coupling : Q') (cutoff shift base : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift) ≈
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff base +
        couplingParametricKTimeShiftBoundaryTargetPartition
          coupling cutoff shift base := by
  have htarget :=
    couplingParametricKTimeShiftCompatiblePartition_eqv_embedded_add_boundary
      coupling cutoff shift base
  have hsource :=
    couplingParametricKCompatiblePartition_eqv_embedded_timeShift
      coupling cutoff shift base
  exact Q'.eqv_trans _ _ _ htarget
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsource))

/-- The translated full-target cylinder numerator is exactly its source
cylinder numerator plus the literal target-boundary event numerator. -/
theorem couplingParametricKTimeShiftFullCylinderNumerator_eqv_source_add_boundary
    (coupling : Q') (cutoff : Nat) {shift base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (base + shift)
        (timeShiftTargetCylinderEvent shift base roots predicate) ≈
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff base
          (sourceCylinderEvent roots predicate) +
        couplingParametricKTimeShiftBoundaryTargetEventNumerator
          coupling cutoff shift base
          (timeShiftTargetCylinderEvent shift base roots predicate) := by
  have htarget :=
    couplingParametricKTimeShiftCompatibleEventNumerator_eqv_embedded_add_boundary
      coupling cutoff shift base
      (timeShiftTargetCylinderEvent shift base roots predicate)
  have hsource :=
    couplingParametricKCompatibleCylinderNumerator_eqv_embedded_timeShift
      coupling cutoff (shift := shift) (base := base) hroots predicate
  exact Q'.eqv_trans _ _ _ htarget
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsource))

/-! ## 4. The exact normalized boundary determinant -/

def couplingParametricKTimeShiftSourceTargetCylinderCrossDifference
    (coupling : Q') (cutoff shift base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (base + shift)
        (timeShiftTargetCylinderEvent shift base roots predicate) *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff base -
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff base (sourceCylinderEvent roots predicate) *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift)

/-- The only finite-volume obstruction to exact normalized covariance: the
boundary event mass times the source partition, minus the source event mass
times the boundary partition. -/
def couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
    (coupling : Q') (cutoff shift base : Nat)
    (roots : List (List Nat)) (predicate : List Bool → Bool) : Q' :=
  couplingParametricKTimeShiftBoundaryTargetEventNumerator
        coupling cutoff shift base
        (timeShiftTargetCylinderEvent shift base roots predicate) *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff base -
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff base (sourceCylinderEvent roots predicate) *
      couplingParametricKTimeShiftBoundaryTargetPartition
        coupling cutoff shift base

theorem couplingParametricKTimeShiftSourceTargetCylinderCrossDifference_eqv_boundary
    (coupling : Q') (cutoff : Nat) {shift base : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKTimeShiftSourceTargetCylinderCrossDifference
        coupling cutoff shift base roots predicate ≈
      couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
        coupling cutoff shift base roots predicate := by
  have hnum :=
    couplingParametricKTimeShiftFullCylinderNumerator_eqv_source_add_boundary
      coupling cutoff (shift := shift) (base := base) hroots predicate
  have hpartition :=
    couplingParametricKTimeShiftFullPartition_eqv_source_add_boundary
      coupling cutoff shift base
  unfold couplingParametricKTimeShiftSourceTargetCylinderCrossDifference
    couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
  refine Q'.eqv_trans _
    ((couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff base (sourceCylinderEvent roots predicate) +
          couplingParametricKTimeShiftBoundaryTargetEventNumerator
            coupling cutoff shift base
            (timeShiftTargetCylinderEvent shift base roots predicate)) *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff base -
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff base (sourceCylinderEvent roots predicate) *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff base +
          couplingParametricKTimeShiftBoundaryTargetPartition
            coupling cutoff shift base)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local hnum (Q'.eqv_refl _))
      (mul_eqv_both_local (Q'.eqv_refl _) hpartition)
  · exact addMul_sub_mulAdd_eqv_cross_local _ _ _ _

theorem couplingParametricKTimeShiftFullTargetProbability_sub_source_eqv_cross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift)
          (timeShiftTargetCylinderEvent shift base roots predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff base
          (sourceCylinderEvent roots predicate) ≈
      Q'.divPos
        (couplingParametricKTimeShiftSourceTargetCylinderCrossDifference
          coupling cutoff shift base roots predicate)
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (base + shift) *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff base)
        (Q'.mul_pos
          (couplingParametricKCompatibleSupportGasPartition_pos
            hcoupling cutoff (base + shift))
          (couplingParametricKCompatibleSupportGasPartition_pos
            hcoupling cutoff base)) := by
  unfold couplingParametricKCompatibleSupportEventProbability
    couplingParametricKTimeShiftSourceTargetCylinderCrossDifference
  exact divPos_sub_eqv_crossDifference _ _ _ _
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff (base + shift))
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff base)

/-- Exact normalized finite-volume translation formula.  The source law and
the full enlarged target law differ by precisely the boundary determinant;
there is no hidden normalization error. -/
theorem couplingParametricKTimeShiftFullTargetProbability_sub_source_eqv_boundary
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {shift base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift)
          (timeShiftTargetCylinderEvent shift base roots predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff base
          (sourceCylinderEvent roots predicate) ≈
      Q'.divPos
        (couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
          coupling cutoff shift base roots predicate)
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (base + shift) *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff base)
        (Q'.mul_pos
          (couplingParametricKCompatibleSupportGasPartition_pos
            hcoupling cutoff (base + shift))
          (couplingParametricKCompatibleSupportGasPartition_pos
            hcoupling cutoff base)) := by
  have hcross :=
    couplingParametricKTimeShiftFullTargetProbability_sub_source_eqv_cross
      hcoupling cutoff shift base roots predicate
  have hboundary :=
    couplingParametricKTimeShiftSourceTargetCylinderCrossDifference_eqv_boundary
      coupling cutoff (shift := shift) (base := base) hroots predicate
  refine Q'.eqv_trans _ _ _ hcross ?_
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hboundary

/-! ## 5. Machine-checked fence around naive finite covariance -/

/-- Exact finite normalized covariance is equivalent to vanishing of the
literal boundary cross-determinant.  Weight preservation on the embedded
cell alone supplies neither direction of that vanishing statement. -/
theorem couplingParametricKTimeShiftFullTargetProbability_eqv_source_iff_boundary
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {shift base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (base + shift)
        (timeShiftTargetCylinderEvent shift base roots predicate) ≈
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (sourceCylinderEvent roots predicate) ↔
    couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
        coupling cutoff shift base roots predicate ≈ (0 : Q') := by
  let target := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff (base + shift)
    (timeShiftTargetCylinderEvent shift base roots predicate)
  let source := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff base
    (sourceCylinderEvent roots predicate)
  let remainder :=
    couplingParametricKTimeShiftBoundaryCylinderCrossRemainder
      coupling cutoff shift base roots predicate
  let denominator :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift) *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff base
  have hdenominator : (0 : Q') < denominator :=
    Q'.mul_pos
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff (base + shift))
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff base)
  have hdifference : target - source ≈
      Q'.divPos remainder denominator hdenominator := by
    simpa only [target, source, remainder, denominator] using
      (couplingParametricKTimeShiftFullTargetProbability_sub_source_eqv_boundary
        hcoupling cutoff hroots predicate)
  constructor
  · intro hequal
    have hzero : target - source ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right target source (-source) hequal)
        (Q'.add_neg_self_eqv source)
    have hquotient : Q'.divPos remainder denominator hdenominator ≈
        (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hdifference) hzero
    have hmul :
        Q'.divPos remainder denominator hdenominator * denominator ≈
          (0 : Q') * denominator :=
      Q'.mul_eqv_congr_right _ _ denominator hquotient
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.divPos_mul_eqv remainder denominator hdenominator))
      (Q'.eqv_trans _ _ _ hmul (Q'.zero_mul_eqv denominator))
  · intro hremainder
    have hquotient : Q'.divPos remainder denominator hdenominator ≈
        (0 : Q') := by
      unfold Q'.divPos
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right remainder 0
          (Q'.recipPos denominator hdenominator) hremainder)
        (Q'.zero_mul_eqv _)
    have hzero : target - source ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ hdifference hquotient
    have hrestore : target ≈ (target - source) + source :=
      Q'.eqv_trans _ _ _
        (Q'.add_sub_cancel_eqv target source)
        (Q'.add_comm_eqv source (target - source))
    exact Q'.eqv_trans _ _ _ hrestore
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (target - source) 0 source hzero)
        (Q'.eqv_of_eq (Q'.zero_add' source)))

#print axioms divPos_sub_eqv_crossDifference
#print axioms couplingParametricKTimeShiftBoundaryTargetPartition_nonnegative
#print axioms couplingParametricKTimeShiftBoundaryTargetEventNumerator_nonnegative
#print axioms couplingParametricKTimeShiftFullPartition_eqv_source_add_boundary
#print axioms couplingParametricKTimeShiftFullCylinderNumerator_eqv_source_add_boundary
#print axioms couplingParametricKTimeShiftSourceTargetCylinderCrossDifference_eqv_boundary
#print axioms couplingParametricKTimeShiftFullTargetProbability_sub_source_eqv_boundary
#print axioms couplingParametricKTimeShiftFullTargetProbability_eqv_source_iff_boundary

end YMGap.Continuum.Z4TimeShiftedFiniteNormalizedCovarianceRemainder
