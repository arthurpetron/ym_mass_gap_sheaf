/-
# Dense BF4 radical descent from pointwise cutoff Cauchy data

The cutoff Markov action is exactly contractive at the cutoff where it is
evaluated.  Its finite-linear recoding also preserves the explicit inner
regularity rate of the limiting squared distance.  Consequently, once the
cutoff pays that input rate, the limiting output distance is bounded by the
limiting input distance plus an explicit rational slack.

For a limiting-radical-null pair, sample this estimate with half the requested
closeness tolerance.  The remaining half absorbs the input null distance.
This constructs the dense radical-closeness datum directly from any family of
pointwise cross-cutoff Cauchy moduli.  Dense radical descent is therefore not
an independent analytic hypothesis.

The genuinely open completion frontier is unchanged: arbitrary completion
representatives still require a cutoff/action diagonal construction.

## Axiom gate

Only explicit inner rates, rational slack splitting, eventual order, and the
already proved finite-cutoff contraction are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The squared-distance rate is invariant -/

/-- Markov recoding preserves the explicit inner approximation rate of the
limiting squared distance exactly. -/
theorem physicalLinearDistSqInnerRegularity_markov_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (physicalLinearDistSqInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).rate epsilon =
      (physicalLinearDistSqInnerRegularity
        hw0 hw1 half left right).rate epsilon := by
  change
    (innerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half (sub left right))
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half (sub left right))).rate epsilon =
      (innerLimitInnerRegularity hw0 hw1 half
        (sub left right) (sub left right)).rate epsilon
  exact innerLimitInnerRegularity_markov_self_rate_eq
    hw0 hw1 half cutoff (sub left right) epsilon

/-! ## 2. Limiting nonexpansiveness with an explicit slack -/

/-- If one cutoff pays the input squared-distance inner rate at half the
requested tolerance, the limiting distance between its two Markov images is
at most the limiting input distance plus that tolerance. -/
theorem physicalLinearDistSq_markovCutoffAction_le_add
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hcutoff :
      (physicalLinearDistSqInnerRegularity
        hw0 hw1 half left right).rate
          (HalfPow.half * epsilon) <= cutoff) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half left)
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half right))
      (CReal.add
        (physicalLinearDistSq hw0 hw1 half left right)
        (CReal.ofQ' epsilon)) := by
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  let input := physicalLinearDistSq hw0 hw1 half left right
  let output := physicalLinearDistSq hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half left)
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half right)
  let inputRegularity := physicalLinearDistSqInnerRegularity
    hw0 hw1 half left right
  let outputRegularity := physicalLinearDistSqInnerRegularity hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half left)
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half right)
  have houtputCutoff : outputRegularity.rate q <= cutoff := by
    rw [physicalLinearDistSqInnerRegularity_markov_rate_eq]
    exact hcutoff
  intro delta hdelta
  refine ⟨inputRegularity.rate q, fun stage hstage => ?_⟩
  have houtputStage : outputRegularity.rate q <= stage := by
    rw [physicalLinearDistSqInnerRegularity_markov_rate_eq]
    exact hstage
  obtain ⟨houtput, _⟩ := outputRegularity.regular q hq
    stage cutoff houtputStage houtputCutoff
  obtain ⟨hinput, _⟩ := inputRegularity.regular q hq
    cutoff stage hcutoff hstage
  have hfinite := physicalLinearDistSq_markovCutoffAction_approx_le
    hw0 hw1 half cutoff left right
  have hchain : output.approx stage <= input.approx stage + (q + q) :=
    Q'.le_trans' _ _ _ houtput
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ q hfinite)
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ q hinput)
          (Q'.le_of_eqv (Q'.add_assoc_eqv _ q q))))
  have htwo : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_eqv_congr_left
        (input.approx stage) (q + q) epsilon htwo))
      (Q'.add_le_self_of_nonneg
        (input.approx stage + epsilon) delta (Q'.le_of_lt hdelta)))

/-! ## 3. Dense radical descent is derived data -/

/-- A limiting-null dense input pair gives explicitly close Markov cutoff
image sequences.  The modulus is the input inner rate at one quarter of the
requested tolerance. -/
def centralPhysicalLinearMarkovCutoffCauchyCloseOfNull
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {left right : CentralPhysicalLinearObservable}
    (hnull : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Null left right) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalLinearMarkovCutoffCauchy
        (pointwise.modulus left))
      (centralPhysicalLinearMarkovCutoffCauchy
        (pointwise.modulus right)) where
  modulus := fun epsilon =>
    (physicalLinearDistSqInnerRegularity
      hw0 hw1 half left right).rate
        (HalfPow.half * (HalfPow.half * epsilon))
  close := by
    intro epsilon hepsilon cutoff hcutoff
    let slack := HalfPow.half * epsilon
    have hslack : (0 : Q') < slack :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hmarkov := physicalLinearDistSq_markovCutoffAction_le_add
      hw0 hw1 half cutoff left right slack hslack hcutoff
    have hnullSlack : CReal.leEv
        (CReal.add
          (physicalLinearDistSq hw0 hw1 half left right)
          (CReal.ofQ' slack))
        (CReal.add CReal.czero (CReal.ofQ' slack)) :=
      CReal.leEv_add (CReal.leEv_of_equiv hnull)
        (CReal.leEv_refl (CReal.ofQ' slack))
    have hslackLe : slack <= epsilon :=
      Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg slack slack (Q'.le_of_lt hslack))
        (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
    have hzeroSlackLe : (0 : Q') + slack <= epsilon := by
      rw [Q'.zero_add']
      exact hslackLe
    have htoEpsilon : CReal.leEv
        (CReal.add CReal.czero (CReal.ofQ' slack))
        (CReal.ofQ' epsilon) :=
      by
        rw [show CReal.czero = CReal.ofQ' 0 from rfl, CReal.ofQ'_add]
        exact CReal.leEv_of_le
          (CReal.ofQ'_le_ofQ' hzeroSlackLe)
    exact CReal.leEv_trans hmarkov
      (CReal.leEv_trans hnullSlack htoEpsilon)

/-- Any pointwise family of Markov cross-cutoff Cauchy moduli automatically
supplies the formerly separate dense radical-descent field. -/
def CentralPhysicalLinearMarkovDenseCauchyData.toDenseRadicalData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseRadicalData hw0 hw1 half where
  pointwise := pointwise
  radicalClose := centralPhysicalLinearMarkovCutoffCauchyCloseOfNull pointwise

#print axioms physicalLinearDistSqInnerRegularity_markov_rate_eq
#print axioms physicalLinearDistSq_markovCutoffAction_le_add
#print axioms centralPhysicalLinearMarkovCutoffCauchyCloseOfNull
#print axioms CentralPhysicalLinearMarkovDenseCauchyData.toDenseRadicalData

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy
