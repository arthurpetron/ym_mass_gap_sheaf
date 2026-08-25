/-
# Two-lane variation factorization for the support-aware BF4 debt

The automatic support-aware margin is

  (half * supported conditional-kernel floor) / (one + routed-load maximum).

Consequently its reciprocal condition number has exactly two independently
estimable cutoff streams:

* the positive routed-load denominator; and
* the reciprocal of the positive supported-kernel numerator.

This module compiles summable variation certificates for those two streams,
under positive uniform ceilings, into summable variation of their product and
then of the normalized capacity debt.  Scaling by the already fixed shared
coercivity floor and setoid transport are serial algebraic consumers after the
two analytic lanes meet.

Every definition remains attached to the same routing, finite vacuum-sector
carrier, physical conditional kernel, and routed transition-product load.
The canonical loop-erased routing is exposed as a sequence inhabitant, but no
variation or ceiling certificate is inhabited for it or for an adaptive
routing.  The fixed anchor is not an asymptotically free trajectory.  No
thermodynamic or continuum limit, continuum Yang--Mills theory, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (product : a * denominator ≈ numerator) :
    a ≈ Q'.divPos numerator denominator denominator_pos := by
  apply Q'.mul_left_cancel_of_pos denominator_pos
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv denominator a) ?_
  refine Q'.eqv_trans _ _ _ product ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv denominator
      (Q'.divPos numerator denominator denominator_pos)) ?_
  exact Q'.divPos_mul_eqv numerator denominator denominator_pos

private theorem divPos_eqv_of_eqv_mul_local
    {numerator denominator quotient : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (factor : numerator ≈ quotient * denominator) :
    Q'.divPos numerator denominator denominator_pos ≈ quotient := by
  show numerator * Q'.recipPos denominator denominator_pos ≈ quotient
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ factor) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv quotient denominator
      (Q'.recipPos denominator denominator_pos)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left quotient _ _
      (Q'.mul_recipPos_eqv denominator denominator_pos)) ?_
  exact Q'.mul_one_eqv quotient

/-! ## 1. The exact two cutoff streams -/

/-- Half the supported conditional-kernel floor: the numerator of the
automatic capacity proxy. -/
def anchorAdaptiveSupportedKernelNumerator
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  HalfPow.half *
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
      (routing K)

theorem anchorAdaptiveSupportedKernelNumerator_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveSupportedKernelNumerator routing K := by
  unfold anchorAdaptiveSupportedKernelNumerator
  exact Q'.mul_pos (by decide)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
      (routing K))

/-- One plus the maximum literal routed transition-product load: the
denominator of the automatic capacity proxy. -/
def anchorAdaptiveRoutedLoadDenominator
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
    (routing K)

theorem anchorAdaptiveRoutedLoadDenominator_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveRoutedLoadDenominator routing K :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator_pos
    (routing K)

/-- The inverse numerator is kept as its own analytic stream. -/
def anchorAdaptiveInverseSupportedKernelNumerator
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  Q'.recipPos
    (anchorAdaptiveSupportedKernelNumerator routing K)
    (anchorAdaptiveSupportedKernelNumerator_pos routing K)

theorem anchorAdaptiveInverseSupportedKernelNumerator_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveInverseSupportedKernelNumerator routing K :=
  Q'.recipPos_pos _ _

/-- The reciprocal automatic proxy, definitionally the product of the two
independent streams above. -/
def anchorAdaptiveSupportCapacityReciprocalProxy
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  Q'.divPos
    (anchorAdaptiveRoutedLoadDenominator routing K)
    (anchorAdaptiveSupportedKernelNumerator routing K)
    (anchorAdaptiveSupportedKernelNumerator_pos routing K)

theorem anchorAdaptiveSupportCapacityReciprocalProxy_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveSupportCapacityReciprocalProxy routing K :=
  Q'.divPos_pos _ _ _ (anchorAdaptiveRoutedLoadDenominator_pos routing K)

/-! ## 2. Exact factorization back to the same automatic margin and debt -/

/-- The reciprocal proxy cancels the automatic support-aware margin. -/
theorem anchorAdaptiveSupportCapacityReciprocalProxy_mul_marginLower_eqv_one
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    anchorAdaptiveSupportCapacityReciprocalProxy routing K *
        anchorAdaptiveSupportCapacityMarginLower routing K ≈ (1 : Q') := by
  let numerator := anchorAdaptiveSupportedKernelNumerator routing K
  let denominator := anchorAdaptiveRoutedLoadDenominator routing K
  let reciprocal := anchorAdaptiveSupportCapacityReciprocalProxy routing K
  let margin := anchorAdaptiveSupportCapacityMarginLower routing K
  have numerator_pos : (0 : Q') < numerator :=
    anchorAdaptiveSupportedKernelNumerator_pos routing K
  have denominator_pos : (0 : Q') < denominator :=
    anchorAdaptiveRoutedLoadDenominator_pos routing K
  have reciprocal_mul_numerator : reciprocal * numerator ≈ denominator := by
    unfold reciprocal anchorAdaptiveSupportCapacityReciprocalProxy
    exact Q'.divPos_mul_eqv denominator numerator numerator_pos
  have margin_mul_denominator : margin * denominator ≈ numerator := by
    unfold margin anchorAdaptiveSupportCapacityMarginLower
    unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
    change
      Q'.divPos numerator denominator denominator_pos * denominator ≈
        numerator
    exact Q'.divPos_mul_eqv numerator denominator denominator_pos
  have product_mul_denominator :
      (reciprocal * margin) * denominator ≈ denominator := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv reciprocal margin denominator) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left reciprocal _ _ margin_mul_denominator) ?_
    exact reciprocal_mul_numerator
  have product_eqv_self_division :
      reciprocal * margin ≈
        Q'.divPos denominator denominator denominator_pos :=
    eqv_divPos_of_mul_local denominator_pos product_mul_denominator
  refine Q'.eqv_trans _ _ _ product_eqv_self_division ?_
  unfold Q'.divPos
  exact Q'.mul_recipPos_eqv denominator denominator_pos

/-- The normalized automatic capacity debt is the fixed shared coercivity
floor times the reciprocal proxy. -/
theorem anchorAdaptiveSupportCapacityDebt_eqv_sharedFloor_mul_reciprocalProxy
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    anchorAdaptiveSupportCapacityDebt routing K ≈
      anchorAdaptiveSharedCoercivityFloor *
        anchorAdaptiveSupportCapacityReciprocalProxy routing K := by
  let margin := anchorAdaptiveSupportCapacityMarginLower routing K
  let reciprocal := anchorAdaptiveSupportCapacityReciprocalProxy routing K
  have margin_pos : (0 : Q') < margin :=
    anchorAdaptiveSupportCapacityMarginLower_pos routing K
  have cancellation : reciprocal * margin ≈ (1 : Q') :=
    anchorAdaptiveSupportCapacityReciprocalProxy_mul_marginLower_eqv_one
      routing K
  have factor : anchorAdaptiveSharedCoercivityFloor ≈
      (anchorAdaptiveSharedCoercivityFloor * reciprocal) * margin := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv anchorAdaptiveSharedCoercivityFloor reciprocal margin) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left anchorAdaptiveSharedCoercivityFloor _ _
        cancellation) ?_
    exact Q'.mul_one_eqv anchorAdaptiveSharedCoercivityFloor
  unfold anchorAdaptiveSupportCapacityDebt
  unfold anchorAdaptiveFiniteCapacityDebt
  exact divPos_eqv_of_eqv_mul_local margin_pos factor

/-! ## 3. Parallel component compilers and their serial join -/

/-- Join the two independent variation certificates at the product boundary.
The only cross-lane information required is one positive uniform ceiling for
each stream. -/
def anchorAdaptiveSupportCapacityReciprocalProxyVariationOfComponents
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (loadVariation : SummableRationalStepVariation
      (anchorAdaptiveRoutedLoadDenominator routing))
    (inverseKernelVariation : SummableRationalStepVariation
      (anchorAdaptiveInverseSupportedKernelNumerator routing))
    (loadCeiling inverseKernelCeiling : Q')
    (loadCeiling_pos : (0 : Q') < loadCeiling)
    (inverseKernelCeiling_pos : (0 : Q') < inverseKernelCeiling)
    (load_le : forall K,
      anchorAdaptiveRoutedLoadDenominator routing K <= loadCeiling)
    (inverseKernel_le : forall K,
      anchorAdaptiveInverseSupportedKernelNumerator routing K <=
        inverseKernelCeiling) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityReciprocalProxy routing) := by
  change SummableRationalStepVariation
    (fun K =>
      anchorAdaptiveRoutedLoadDenominator routing K *
        anchorAdaptiveInverseSupportedKernelNumerator routing K)
  exact mulOfCeilings
    loadVariation inverseKernelVariation
    loadCeiling inverseKernelCeiling
    loadCeiling_pos inverseKernelCeiling_pos
    (fun K => Q'.le_of_lt
      (anchorAdaptiveRoutedLoadDenominator_pos routing K))
    (fun K => Q'.le_of_lt
      (anchorAdaptiveInverseSupportedKernelNumerator_pos routing K))
    load_le inverseKernel_le

/-- Serially scale the joined condition-number variation by the fixed shared
floor and transport it through the exact debt factorization. -/
def anchorAdaptiveSupportCapacityDebtVariationOfComponents
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (loadVariation : SummableRationalStepVariation
      (anchorAdaptiveRoutedLoadDenominator routing))
    (inverseKernelVariation : SummableRationalStepVariation
      (anchorAdaptiveInverseSupportedKernelNumerator routing))
    (loadCeiling inverseKernelCeiling : Q')
    (loadCeiling_pos : (0 : Q') < loadCeiling)
    (inverseKernelCeiling_pos : (0 : Q') < inverseKernelCeiling)
    (load_le : forall K,
      anchorAdaptiveRoutedLoadDenominator routing K <= loadCeiling)
    (inverseKernel_le : forall K,
      anchorAdaptiveInverseSupportedKernelNumerator routing K <=
        inverseKernelCeiling) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt routing) := by
  let reciprocalVariation :=
    anchorAdaptiveSupportCapacityReciprocalProxyVariationOfComponents
      routing loadVariation inverseKernelVariation
      loadCeiling inverseKernelCeiling
      loadCeiling_pos inverseKernelCeiling_pos load_le inverseKernel_le
  let scaledVariation := scale reciprocalVariation
    anchorAdaptiveSharedCoercivityFloor
    anchorAdaptiveSharedCoercivityFloor_pos
  exact ofPointwiseEqv scaledVariation (fun K =>
    Q'.eqv_symm
      (anchorAdaptiveSupportCapacityDebt_eqv_sharedFloor_mul_reciprocalProxy
        routing K))

/-- End-to-end fixed-anchor compiler after the two independent analytic lanes
have supplied their variation and ceiling data. -/
def anchorAdaptiveSupportCapacityDebtVariationFromComponents
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (loadVariation : SummableRationalStepVariation
      (anchorAdaptiveRoutedLoadDenominator routing))
    (inverseKernelVariation : SummableRationalStepVariation
      (anchorAdaptiveInverseSupportedKernelNumerator routing))
    (loadCeiling inverseKernelCeiling : Q')
    (loadCeiling_pos : (0 : Q') < loadCeiling)
    (inverseKernelCeiling_pos : (0 : Q') < inverseKernelCeiling)
    (load_le : forall K,
      anchorAdaptiveRoutedLoadDenominator routing K <= loadCeiling)
    (inverseKernel_le : forall K,
      anchorAdaptiveInverseSupportedKernelNumerator routing K <=
        inverseKernelCeiling)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorAdaptiveSupportCapacityDebtVariationOfComponents
        routing loadVariation inverseKernelVariation
        loadCeiling inverseKernelCeiling
        loadCeiling_pos inverseKernelCeiling_pos
        load_le inverseKernel_le).tailControl.tailRate budget = 0)
    (initial_closure :
      anchorAdaptiveSupportCapacityDebt routing 0 + budget <= (1 : Q')) :
    AnchorAdaptiveFiniteCapacityDebtVariation :=
  anchorAdaptiveSupportCapacityDebtVariation
    routing
    (anchorAdaptiveSupportCapacityDebtVariationOfComponents
      routing loadVariation inverseKernelVariation
      loadCeiling inverseKernelCeiling
      loadCeiling_pos inverseKernelCeiling_pos
      load_le inverseKernel_le)
    budget budget_pos budget_from_zero initial_closure

/-! ## 4. The canonical proof-path specialization -/

/-- The canonical loop-erased routing at every anchor cutoff.  This removes
routing construction from the canonical proof path without asserting that
its two analytic streams obey the required uniform estimates. -/
def anchorCanonicalPositiveRoutingSequence :
    AnchorAdaptivePositiveRoutingSequence :=
  fun K =>
    canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) K

/-- The two-lane compiler specialized to the canonical routing.  An adaptive
proof path uses the general compiler above; the two paths share the same
observable-connected product consumer. -/
def anchorCanonicalSupportCapacityDebtVariationOfComponents
    (loadVariation : SummableRationalStepVariation
      (anchorAdaptiveRoutedLoadDenominator
        anchorCanonicalPositiveRoutingSequence))
    (inverseKernelVariation : SummableRationalStepVariation
      (anchorAdaptiveInverseSupportedKernelNumerator
        anchorCanonicalPositiveRoutingSequence))
    (loadCeiling inverseKernelCeiling : Q')
    (loadCeiling_pos : (0 : Q') < loadCeiling)
    (inverseKernelCeiling_pos : (0 : Q') < inverseKernelCeiling)
    (load_le : forall K,
      anchorAdaptiveRoutedLoadDenominator
        anchorCanonicalPositiveRoutingSequence K <= loadCeiling)
    (inverseKernel_le : forall K,
      anchorAdaptiveInverseSupportedKernelNumerator
        anchorCanonicalPositiveRoutingSequence K <= inverseKernelCeiling) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt
        anchorCanonicalPositiveRoutingSequence) :=
  anchorAdaptiveSupportCapacityDebtVariationOfComponents
    anchorCanonicalPositiveRoutingSequence
    loadVariation inverseKernelVariation
    loadCeiling inverseKernelCeiling
    loadCeiling_pos inverseKernelCeiling_pos
    load_le inverseKernel_le

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorAdaptiveSupportCapacityReciprocalProxy_mul_marginLower_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorAdaptiveSupportCapacityDebt_eqv_sharedFloor_mul_reciprocalProxy
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorAdaptiveSupportCapacityReciprocalProxyVariationOfComponents
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorAdaptiveSupportCapacityDebtVariationOfComponents
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorAdaptiveSupportCapacityDebtVariationFromComponents
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorCanonicalPositiveRoutingSequence
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.anchorCanonicalSupportCapacityDebtVariationOfComponents
