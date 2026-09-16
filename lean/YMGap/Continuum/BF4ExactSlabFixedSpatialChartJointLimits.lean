/-
# Both orders of cutoff and boundary-time limit for the reflected chart

At a fixed boundary depth the cutoff limit is literally the existing
original selected-chain expectation. The rectangular estimate compares
its actual approximations with the joint diagonal limit. Taking time
first gives the same result, and the existing intrinsic-pairing pin
identifies the cutoff limit of the actual fixed-stage reflected pairing.

The computed maximum of the two presentation radii defines a canonical
cutoff-removed scalar pairing, with its QCauchy data retained separately.
Every other valid chart yields an equivalent scalar by uniqueness of the
same fixed-stage pairing limit. No representative is selected, no cutoff
estimate uniform in arbitrary time length is assumed, and spatial width
and nome remain fixed. This is not a new completed carrier or continuum
theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (expectation)
open YMGap.Continuum.BoundedRationalCauchyProduct (representativeCauchy)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width H : Nat) (x y : PhysicalSpan width)

/-- The cutoff limit of the actual finite chart, without radius hypotheses. -/
def chartCutoffExpectation (t : Nat) : CReal :=
  ofQ'CauchySeq (fun stage => chartScalar hw0 hw1 width stage H x y t)
    (chartCutoffCauchy hw0 hw1 width H x y t)

/-- The cutoff-first object is the existing original expectation with its
unchanged extent, chain, insertion and partition. -/
theorem chartCutoffExpectation_original (t : Nat) :
    chartCutoffExpectation hw0 hw1 width H x y t =
      let E := adjacentEvenExtent (width+t+H)
      let start := width+1
      expectation w hw0 hw1 E (chainIds E width start (t+(2*H+t)))
        (fun _ hi => chainIds_physical hi)
        (polyMul (placedSpan E (start+t) (mirrorSpan H (encodeChart H x.val)))
          (placedSpan E (start+t) (encodeChart H y.val))) := rfl

theorem chartCutoff_converges (t : Nat) :
    ConvergesTo (fun stage => ofQ' (chartScalar hw0 hw1 width stage H x y t))
      (chartCutoffExpectation hw0 hw1 width H x y t) :=
  convergesTo_ofQ'CauchySeq _ (chartCutoffCauchy hw0 hw1 width H x y t)

variable (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)

/-- Both approximation-index thresholds are explicit, including the
cutoff threshold at the one chosen intermediate boundary depth. -/
theorem chartCutoffExpectation_approx_joint
    (epsilon : Q') (he : (0 : Q') < epsilon) (t a b : Nat)
    (ht : chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon ≤ t)
    (ha : chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon ≤ a)
    (hb : chartJointModulus hw0 hw1 width H x y hx hy epsilon ≤ b) :
    (chartCutoffExpectation hw0 hw1 width H x y t).approx a ≤
        (chartJointLimit hw0 hw1 width H x y hx hy).approx b + epsilon ∧
      (chartJointLimit hw0 hw1 width H x y hx hy).approx b ≤
        (chartCutoffExpectation hw0 hw1 width H x y t).approx a + epsilon := by
  let c := chartCutoffCauchy hw0 hw1 width H x y t
  exact chartJoint_approx hw0 hw1 width H x y hx hy epsilon he
    (QMhat _ c a) t b (Nat.le_trans ha (self_le_QMhat _ c a)) ht hb

/-- Cutoff first and boundary time second gives the constructed joint limit. -/
theorem chartCutoffExpectation_converges_joint :
    ConvergesTo (chartCutoffExpectation hw0 hw1 width H x y)
      (chartJointLimit hw0 hw1 width H x y hx hy) := by
  intro epsilon he
  refine ⟨chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon, fun t ht =>
    ⟨chartJointModulus hw0 hw1 width H x y hx hy epsilon, fun k hk => ?_⟩⟩
  exact chartCutoffExpectation_approx_joint hw0 hw1 width H x y hx hy epsilon he
    t k k ht (Nat.le_trans (Nat.le_max_right _ _) hk) hk

/-- The direct time-first chart limit, with the original computed modulus. -/
def chartTimeLimit (stage : Nat) : CReal :=
  ofQ'CauchySeq (fun t => chartScalar hw0 hw1 width stage H x y t)
    (chartCauchy hw0 hw1 width stage H x y hx hy)

theorem chartTimeLimit_approx_joint
    (epsilon : Q') (he : (0 : Q') < epsilon) (stage a b : Nat)
    (hk : chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon ≤ stage)
    (ha : chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon ≤ a)
    (hb : chartJointModulus hw0 hw1 width H x y hx hy epsilon ≤ b) :
    (chartTimeLimit hw0 hw1 width H x y hx hy stage).approx a ≤
        (chartJointLimit hw0 hw1 width H x y hx hy).approx b + epsilon ∧
      (chartJointLimit hw0 hw1 width H x y hx hy).approx b ≤
        (chartTimeLimit hw0 hw1 width H x y hx hy stage).approx a + epsilon := by
  let c := chartCauchy hw0 hw1 width stage H x y hx hy
  exact chartJoint_approx hw0 hw1 width H x y hx hy epsilon he
    stage (QMhat _ c a) b hk (Nat.le_trans ha (self_le_QMhat _ c a)) hb

/-- Boundary time first and cutoff second gives the SAME joint limit. -/
theorem chartTimeLimit_converges_joint :
    ConvergesTo (chartTimeLimit hw0 hw1 width H x y hx hy)
      (chartJointLimit hw0 hw1 width H x y hx hy) := by
  intro epsilon he
  refine ⟨chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon, fun stage hk =>
    ⟨chartJointModulus hw0 hw1 width H x y hx hy epsilon, fun k hp => ?_⟩⟩
  exact chartTimeLimit_approx_joint hw0 hw1 width H x y hx hy epsilon he
    stage k k hk (Nat.le_trans (Nat.le_max_left _ _) hp) hp

/-- The existing intrinsic reflected pairing, not a newly substituted
stage-wise form, converges to this joint scalar. -/
theorem pairing_converges_chartJoint :
    ConvergesTo (fun stage => pairing hw0 hw1 width x.val y.val stage)
      (chartJointLimit hw0 hw1 width H x y hx hy) :=
  TrigAddCReal.convergesTo_congr_seq
    (fun stage => chartScalar_limit hw0 hw1 width stage H x y hx hy)
    (chartTimeLimit_converges_joint hw0 hw1 width H x y hx hy)

/-- Canonical cutoff-removed reflected scalar, using the computed common
radius rather than an existentially chosen chart. -/
def jointPairing : CReal :=
  chartJointLimit hw0 hw1 width (max (radius x.val) (radius y.val)) x y
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Actual approximation-modulus data of the canonical joint scalar. -/
def jointPairingCauchy : QCauchy (jointPairing hw0 hw1 width x y).approx :=
  representativeCauchy _ (chartJointCauchy hw0 hw1 width
    (max (radius x.val) (radius y.val)) x y (Nat.le_max_left _ _) (Nat.le_max_right _ _))

theorem pairing_converges_jointPairing :
    ConvergesTo (fun stage => pairing hw0 hw1 width x.val y.val stage)
      (jointPairing hw0 hw1 width x y) :=
  pairing_converges_chartJoint hw0 hw1 width (max (radius x.val) (radius y.val))
    x y (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Every valid common chart computes the SAME cutoff-removed pairing. -/
theorem jointPairing_chart :
    Equiv (jointPairing hw0 hw1 width x y)
      (chartJointLimit hw0 hw1 width H x y hx hy) :=
  Equiv_of_limit_of_equal
    (fun stage => Equiv.refl (pairing hw0 hw1 width x.val y.val stage))
    (pairing_converges_jointPairing hw0 hw1 width x y)
    (pairing_converges_chartJoint hw0 hw1 width H x y hx hy)

end YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartCutoffExpectation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartCutoffExpectation_original
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartCutoff_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartCutoffExpectation_approx_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartCutoffExpectation_converges_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartTimeLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartTimeLimit_approx_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.chartTimeLimit_converges_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.pairing_converges_chartJoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.jointPairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.jointPairingCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.pairing_converges_jointPairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits.jointPairing_chart
