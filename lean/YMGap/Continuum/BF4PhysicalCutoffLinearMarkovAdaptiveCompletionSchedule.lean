/-
# Adaptive two-index schedule for the completed BF4 Markov action

The raw completion modulus asks every arbitrary representative to make
`P_n(X_n)` Cauchy at the literal same index.  That demand is too strong:
finite-linear syntax, and hence its explicit inner rate, can grow faster than
the numeric sequence index.

This file constructs the replacement schedule.  At action cutoff `K`, a slow
diagonal selects the largest input index `i` whose cumulative obligations fit
inside `K`.  The `i`-th obligation pays, for every earlier anchor `j <= i`,

* the regularized cross-cutoff rate of the fixed observable `X_j`; and
* the regularized inner rate of the squared distance from `X_i` to `X_j`.

The selector is cofinal and one simultaneous admissibility theorem exposes
both paid rates at arbitrary positive tolerances.  This is the quantitative
schedule required to prove that `K |-> P_K(X_{i(K)})` is Cauchy.

## Axiom gate

Only finite running maxima, bounded search, explicit Type-level moduli, and
rational tolerance regularization are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Antitone pointwise cross-cutoff rates -/

/-- Running-maximum regularization of one supplied pointwise Markov rate. -/
def regularPhysicalLinearMarkovCrossCutoffRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable)
    (epsilon : Q') : Nat :=
  CReal.Gmax
    (fun precision =>
      (pointwise.modulus observable).rate (Q'.invSucc precision))
    (CReal.lv epsilon)

theorem regularPhysicalLinearMarkovCrossCutoffRate_antitone
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    regularPhysicalLinearMarkovCrossCutoffRate
        pointwise observable epsilon <=
      regularPhysicalLinearMarkovCrossCutoffRate
        pointwise observable delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

/-- Regularization produces an equivalent pointwise cross-cutoff modulus with
an antitone tolerance rate. -/
def regularizedPhysicalLinearMarkovCrossCutoffModulus
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable) :
    CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half observable where
  rate := regularPhysicalLinearMarkovCrossCutoffRate pointwise observable
  cauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    let delta := Q'.invSucc (CReal.lv epsilon)
    have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
    have hraw : (pointwise.modulus observable).rate delta <=
        regularPhysicalLinearMarkovCrossCutoffRate
          pointwise observable epsilon :=
      CReal.Gmax_ge
        (fun precision =>
          (pointwise.modulus observable).rate (Q'.invSucc precision))
        (CReal.lv epsilon)
    have hbound := (pointwise.modulus observable).cauchy
      delta hdelta first second
      (Nat.le_trans hraw hfirst) (Nat.le_trans hraw hsecond)
    exact CReal.leEv_trans hbound
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ'
          (CReal.invSucc_lv_le hepsilon)))

/-! ## 2. Regularized limiting nonexpansiveness -/

/-- Regularizing the squared-distance inner witness preserves exact Markov
rate invariance. -/
theorem regularizedPhysicalLinearDistSq_markov_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (regularizedInnerRegularity
      (physicalLinearDistSqInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half left)
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half right))).rate epsilon =
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity
          hw0 hw1 half left right)).rate epsilon := by
  unfold regularizedInnerRegularity regularInnerRate
  apply congrArg (fun rate : Nat -> Nat =>
    CReal.Gmax rate (CReal.lv epsilon))
  funext precision
  exact physicalLinearDistSqInnerRegularity_markov_rate_eq
    hw0 hw1 half cutoff left right (Q'.invSucc precision)

/-- The limiting same-cutoff nonexpansive estimate accepts the antitone
regularized inner witness used by the adaptive schedule. -/
theorem physicalLinearDistSq_markovCutoffAction_le_add_regularized
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hcutoff :
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity
          hw0 hw1 half left right)).rate
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
  let inputRegularity := regularizedInnerRegularity
    (physicalLinearDistSqInnerRegularity hw0 hw1 half left right)
  let outputRegularity := regularizedInnerRegularity
    (physicalLinearDistSqInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right))
  have houtputCutoff : outputRegularity.rate q <= cutoff := by
    rw [regularizedPhysicalLinearDistSq_markov_rate_eq]
    exact hcutoff
  intro delta hdelta
  refine ⟨inputRegularity.rate q, fun stage hstage => ?_⟩
  have houtputStage : outputRegularity.rate q <= stage := by
    rw [regularizedPhysicalLinearDistSq_markov_rate_eq]
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
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_eqv_congr_left
        (input.approx stage) (q + q) epsilon
        (ExpNeg.two_halves epsilon)))
      (Q'.add_le_self_of_nonneg
        (input.approx stage + epsilon) delta (Q'.le_of_lt hdelta)))

/-! ## 3. The cumulative two-index schedule -/

/-- At input index `i`, pay every fixed-anchor action rate and every
same-cutoff distance rate for anchors `j <= i`. -/
def centralPhysicalAdaptiveMarkovRequirement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (index : Nat) : Nat :=
  max
    (CReal.Gmax
      (fun anchor =>
        regularPhysicalLinearMarkovCrossCutoffRate pointwise
          (X.seq anchor) (Q'.invSucc index))
      index)
    (CReal.Gmax
      (fun anchor =>
        (regularizedInnerRegularity
          (physicalLinearDistSqInnerRegularity hw0 hw1 half
            (X.seq index) (X.seq anchor))).rate (Q'.invSucc index))
      index)

def centralPhysicalAdaptiveMarkovSampleRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold : Nat) : Nat :=
  slowThreshold
    (centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X) threshold

def centralPhysicalAdaptiveMarkovSampleIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  slowIndex
    (centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X) stage

theorem centralPhysicalAdaptiveMarkovSampleIndex_cofinal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold stage : Nat)
    (hstage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X threshold <= stage) :
    threshold <= centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X stage :=
  slowIndex_cofinal
    (centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X) threshold stage hstage

private theorem gmax_value_le_of_le
    (value : Nat -> Nat) {anchor index : Nat}
    (hanchor : anchor <= index) :
    value anchor <= CReal.Gmax value index :=
  Nat.le_trans (CReal.Gmax_ge value anchor)
    (CReal.Gmax_mono value anchor index hanchor)

/-- A single late-stage hypothesis simultaneously makes the selected index
cofinal past an arbitrary anchor and pays the fixed-anchor pointwise rate and
the selected-to-anchor distance rate at independently requested tolerances. -/
theorem centralPhysicalAdaptiveMarkov_requirements_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (anchor : Nat)
    (pointwiseTolerance pairTolerance : Q')
    (hpointwiseTolerance : (0 : Q') < pointwiseTolerance)
    (hpairTolerance : (0 : Q') < pairTolerance)
    (stage : Nat)
    (hstage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X
        (max anchor
          (max (CReal.lv pointwiseTolerance)
            (CReal.lv pairTolerance))) <= stage) :
    let index := centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X stage
    anchor <= index /\
    regularPhysicalLinearMarkovCrossCutoffRate
      pointwise (X.seq anchor) pointwiseTolerance <= stage /\
    (regularizedInnerRegularity
      (physicalLinearDistSqInnerRegularity hw0 hw1 half
        (X.seq index) (X.seq anchor))).rate pairTolerance <= stage := by
  let threshold := max anchor
    (max (CReal.lv pointwiseTolerance) (CReal.lv pairTolerance))
  let index := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X stage
  have hindexThreshold : threshold <= index :=
    centralPhysicalAdaptiveMarkovSampleIndex_cofinal
      hw0 hw1 half pointwise X threshold stage hstage
  have hanchor : anchor <= index :=
    Nat.le_trans (Nat.le_max_left _ _) hindexThreshold
  have hpointPrecision : CReal.lv pointwiseTolerance <= index :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      hindexThreshold
  have hpairPrecision : CReal.lv pairTolerance <= index :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      hindexThreshold
  have hzeroRate : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X 0 <=
      centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise X threshold :=
    slowThreshold_mono
      (centralPhysicalAdaptiveMarkovRequirement
        hw0 hw1 half pointwise X) (Nat.zero_le _)
  have hrequirement : centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X index <= stage :=
    required_slowIndex_le
      (centralPhysicalAdaptiveMarkovRequirement
        hw0 hw1 half pointwise X) stage
      (Nat.le_trans hzeroRate hstage)
  have hpointDelta : Q'.invSucc index <= pointwiseTolerance :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hpointPrecision)
      (CReal.invSucc_lv_le hpointwiseTolerance)
  have hpairDelta : Q'.invSucc index <= pairTolerance :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hpairPrecision)
      (CReal.invSucc_lv_le hpairTolerance)
  have hpointAntitone :=
    regularPhysicalLinearMarkovCrossCutoffRate_antitone
      pointwise (X.seq anchor) (Q'.invSucc_pos index) hpointDelta
  have hpointGmax :
      regularPhysicalLinearMarkovCrossCutoffRate
          pointwise (X.seq anchor) (Q'.invSucc index) <=
        CReal.Gmax
          (fun earlier =>
            regularPhysicalLinearMarkovCrossCutoffRate pointwise
              (X.seq earlier) (Q'.invSucc index)) index :=
    gmax_value_le_of_le
      (fun earlier =>
        regularPhysicalLinearMarkovCrossCutoffRate pointwise
          (X.seq earlier) (Q'.invSucc index)) hanchor
  have hpointPaid : regularPhysicalLinearMarkovCrossCutoffRate
      pointwise (X.seq anchor) pointwiseTolerance <= stage :=
    Nat.le_trans hpointAntitone
      (Nat.le_trans hpointGmax
        (Nat.le_trans (Nat.le_max_left _ _) hrequirement))
  have hpairAntitone := regularInnerRate_antitone
    (physicalLinearDistSqInnerRegularity hw0 hw1 half
      (X.seq index) (X.seq anchor))
    (Q'.invSucc_pos index) hpairDelta
  have hpairGmax :
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          (X.seq index) (X.seq anchor))).rate (Q'.invSucc index) <=
        CReal.Gmax
          (fun earlier =>
            (regularizedInnerRegularity
              (physicalLinearDistSqInnerRegularity hw0 hw1 half
                (X.seq index) (X.seq earlier))).rate
                  (Q'.invSucc index)) index :=
    gmax_value_le_of_le
      (fun earlier =>
        (regularizedInnerRegularity
          (physicalLinearDistSqInnerRegularity hw0 hw1 half
            (X.seq index) (X.seq earlier))).rate
              (Q'.invSucc index)) hanchor
  have hpairPaid :
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          (X.seq index) (X.seq anchor))).rate pairTolerance <= stage :=
    Nat.le_trans hpairAntitone
      (Nat.le_trans hpairGmax
        (Nat.le_trans (Nat.le_max_right _ _) hrequirement))
  exact ⟨hanchor, hpointPaid, hpairPaid⟩

#print axioms regularizedPhysicalLinearMarkovCrossCutoffModulus
#print axioms regularizedPhysicalLinearDistSq_markov_rate_eq
#print axioms physicalLinearDistSq_markovCutoffAction_le_add_regularized
#print axioms centralPhysicalAdaptiveMarkovSampleIndex_cofinal
#print axioms centralPhysicalAdaptiveMarkov_requirements_paid

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
