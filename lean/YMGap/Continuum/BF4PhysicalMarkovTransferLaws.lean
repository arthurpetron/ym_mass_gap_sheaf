/-
M2 -- transfer-form laws for the literal reversible BF4 conditional kernel.

The normalized reflected BF4 joint law already supplies a finite reversible
Markov operator on its positive-marginal carrier.  This module proves two
operator-form facts directly on that literal object:

* positivity: `0 <= <f,Tf>` from finite-volume OS positivity;
* the identity form bound: `|<f,Tf>| <= <f,f>` from the normalized symmetric
  joint law and the finite Young-envelope estimate.

Together with the existing self-adjointness theorem, these are the exact
finite transfer-form laws available before completing a Hilbert-space lift.
They do not identify this reflected conditional operator with a Euclidean
one-lattice-step time shift, prove a strict vacuum-complement contraction, or
construct the physical separator.
-/

import YMGap.Continuum.BF4ExactPhysicalPerronReroute

namespace YMGap.Continuum.BF4PhysicalMarkovTransferLaws

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private def zeroJoint (_left _right : EdgeLabelling) : Q' := 0

private theorem finiteJointQuadratic_zeroJoint_eqv
    (states : List EdgeLabelling)
    (coefficient : EdgeLabelling → Q') :
    finiteJointQuadratic states coefficient zeroJoint ≈ 0 := by
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q')) states) _ ?_
    (listQSum_zero states)
  apply listQSum_congr_on
  intro left _
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q')) states) _ ?_
    (listQSum_zero states)
  apply listQSum_congr_on
  intro right _
  exact Q'.mul_zero_eqv (coefficient left * coefficient right)

private theorem add_neg_zero_eqv (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl value)
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

/-- On every retained source row, the normalized reflected joint mass over
the retained target carrier is exactly the physical stationary marginal. -/
theorem centralPhysicalJoint_row_eq_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    listQSum
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source)
        (centralPositiveHalfStates w hw K half) ≈
      centralPhysicalRowMarginal w hw K half source := by
  let states := centralPositiveHalfStates w hw K half
  let marginal := centralPhysicalRowMarginal w hw K half source
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        marginal *
          centralPhysicalConditionalKernel
            w hw K half source target)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact Q'.eqv_symm
      (centralPhysicalMarginal_mul_conditional_eqv_joint hsource)
  refine Q'.eqv_trans _
    (marginal *
      listQSum
        (centralPhysicalConditionalKernel w hw K half source)
        states) _ ?_ ?_
  · exact listQSum_mul_left marginal
      (centralPhysicalConditionalKernel w hw K half source) states
  refine Q'.eqv_trans _ (marginal * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left marginal _ _
      (centralPhysicalConditionalKernel_row_normalized hsource)
  · exact Q'.mul_one_eqv marginal

private theorem centralPhysicalJoint_zero_absRow_eqv_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates w hw K half)
        (centralNormalizedPhysicalReflectedKernel w hw K half)
        zeroJoint source ≈
      centralPhysicalRowMarginal w hw K half source := by
  unfold finiteJointDifferenceAbsRowMass
  refine Q'.eqv_trans _
    (listQSum
      (centralNormalizedPhysicalReflectedKernel w hw K half source)
      (centralPositiveHalfStates w hw K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    have hentryNonnegative :=
      centralNormalizedPhysicalReflectedKernel_nonnegative
        hw K half source target
    have hdropZero :
        centralNormalizedPhysicalReflectedKernel w hw K half source target +
            (-zeroJoint source target) ≈
          centralNormalizedPhysicalReflectedKernel
            w hw K half source target :=
      add_neg_zero_eqv _
    exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr hdropZero)
      (Q'.eqv_of_eq
        (YMGap.Constructive.ExpNeg.abs_of_nonneg hentryNonnegative))
  · exact centralPhysicalJoint_row_eq_marginal hsource

/-- The exact reflected BF4 Markov quadratic is nonnegative.  This is the
finite rational operator-positivity law supplied by OS positivity. -/
theorem centralPhysicalMarkovApply_positive
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralPhysicalWeightedInner w hw K half observable
        (centralPhysicalMarkovApply w hw K half observable) := by
  have hfull :=
    centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      w hw K half observable
  have hjoint :=
    centralPhysicalJointQuadratic_eq_normalizedFull
      w hw K half observable
  have hmarkov :=
    centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw K half observable
  exact Q'.le_trans' _ _ _ hfull
    (Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hjoint)
      (Q'.ge_of_eqv hmarkov))

/-- The exact reflected BF4 Markov quadratic is bounded in absolute value by
the identity quadratic on the same physical stationary carrier. -/
theorem centralPhysicalMarkovApply_abs_form_le_identity
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (observable : EdgeLabelling → Q') :
    Q'.abs
        (centralPhysicalWeightedInner w hw K half observable
          (centralPhysicalMarkovApply w hw K half observable)) ≤
      centralPhysicalWeightedInner w hw K half observable observable := by
  let states := centralPositiveHalfStates w hw K half
  let joint := centralNormalizedPhysicalReflectedKernel w hw K half
  let weight := centralPhysicalRowMarginal w hw K half
  have hperturb :=
    finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable weight joint zeroJoint 1
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      (fun _ _ _ _ => Q'.eqv_refl 0)
      (fun state hstate => by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (centralPhysicalJoint_zero_absRow_eqv_marginal hstate))
          (Q'.le_of_eqv
            (Q'.eqv_symm (Q'.one_mul_eqv (weight state)))))
  have hzero :
      finiteJointQuadratic states observable zeroJoint ≈ 0 :=
    finiteJointQuadratic_zeroJoint_eqv states observable
  have hdropZero :
      finiteJointQuadratic states observable joint +
          (-finiteJointQuadratic states observable zeroJoint) ≈
        finiteJointQuadratic states observable joint := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic states observable joint + (-(0 : Q'))) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hzero)
    · exact add_neg_zero_eqv _
  have hjointBound :
      Q'.abs (centralPhysicalJointQuadratic w hw K half observable) ≤
        1 * finiteWeightedSquare states weight observable := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hdropZero)))
      hperturb
  have hmarkov :=
    centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw K half observable
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hmarkov)) ?_
  refine Q'.le_trans' _ _ _ hjointBound ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.one_mul_eqv (finiteWeightedSquare states weight observable))
      (finiteWeightedSquare_physical_eqv_inner
        w hw K half observable))

/-- Positive identity-form interval for the literal reversible BF4 operator. -/
theorem centralPhysicalMarkovApply_form_interval
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
        centralPhysicalWeightedInner w hw K half observable
          (centralPhysicalMarkovApply w hw K half observable) ∧
      centralPhysicalWeightedInner w hw K half observable
          (centralPhysicalMarkovApply w hw K half observable) ≤
        centralPhysicalWeightedInner w hw K half observable observable := by
  exact ⟨centralPhysicalMarkovApply_positive w hw K half observable,
    Q'.le_trans' _ _ _
      (Q'.le_abs_self _)
      (centralPhysicalMarkovApply_abs_form_le_identity
        w hw K half observable)⟩

end YMGap.Continuum.BF4PhysicalMarkovTransferLaws

#print axioms YMGap.Continuum.BF4PhysicalMarkovTransferLaws.centralPhysicalJoint_row_eq_marginal
#print axioms YMGap.Continuum.BF4PhysicalMarkovTransferLaws.centralPhysicalMarkovApply_positive
#print axioms YMGap.Continuum.BF4PhysicalMarkovTransferLaws.centralPhysicalMarkovApply_abs_form_le_identity
#print axioms YMGap.Continuum.BF4PhysicalMarkovTransferLaws.centralPhysicalMarkovApply_form_interval
