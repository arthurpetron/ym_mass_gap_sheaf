/-
# Adaptive graph norms for the completed BF4 transfer

The prior module replaces every cutoff-completion representative by a close,
cofinally sampled representative whose finite stage pays the regularized
self-pair and vacuum-pair inner rates.  Markov syntax preserves those rates.

This file uses that normalized representative to diagonalize all four raw
moments, proves completed vacuum-pairing invariance, transports exact finite
centering, and compiles the fixed-nome finite sixteenth into strict contraction
of the actual cutoff-removed transfer.

The result removes the separate graph-cofinality input.  It remains conditional
on the honest Markov completion modulus and fixed-nome finite gap certificate;
neither is inhabited here.

## Axiom gate

Only explicit constructive rates, cofinal reindexing, finite centering,
constructive-real limit algebra, and quotient soundness are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality.CentralPhysicalLinearMarkovGraphNormInnerCofinality
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A diagonal theorem for a regularized inner modulus -/

/-- The outer pairing diagonal converges whenever its own stage pays the
regularized inner modulus.  Unlike the earlier same-index theorem, this form
accepts the equivalent antitone regularity witness used by the adaptive
sampler. -/
theorem physicalCauchyPairingRegularizedDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stageRate : Q' -> Nat)
    (rate_le_stage : forall
      (epsilon : Q'), (0 : Q') < epsilon ->
      forall stage, stageRate epsilon <= stage ->
        (regularizedInnerRegularity
          (innerLimitInnerRegularity hw0 hw1 half
            (X.seq stage) (Y.seq stage))).rate epsilon <= stage) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (X.seq stage) (Y.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half X Y) := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨outerStage, houterStage⟩ :=
    physicalCauchyPairingSeq_converges hw0 hw1 half X Y q hq
  refine ⟨max outerStage (stageRate q), fun stage hstage => ?_⟩
  have houter : outerStage <= stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hrateStage : stageRate q <= stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  let innerRegularity := regularizedInnerRegularity
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq stage) (Y.seq stage))
  let innerRate := innerRegularity.rate q
  have hinnerRate : innerRate <= stage :=
    rate_le_stage q hq stage hrateStage
  obtain ⟨outerApprox, houterApprox⟩ := houterStage stage houter
  refine ⟨max outerApprox innerRate, fun k hk => ?_⟩
  have hkOuter : outerApprox <= k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hkInner : innerRate <= k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hinnerForward, hinnerBackward⟩ :=
    innerRegularity.regular q hq stage k hinnerRate hkInner
  obtain ⟨houterForward, houterBackward⟩ := houterApprox k hkOuter
  have htwo : (q + q) ≈ epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain := Q'.le_trans' _ _ _ hinnerForward
      (Q'.add_le_add_right _ _ q houterForward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))
  · have hchain := Q'.le_trans' _ _ _ houterBackward
      (Q'.add_le_add_right _ _ q hinnerBackward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))

/-! ## 2. The sampler pays all four graph rates -/

/-- Regularization preserves exact Markov self-rate invariance. -/
theorem regularizedInnerRegularity_markov_self_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (observable : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half observable)
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half observable))).rate epsilon =
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          observable observable)).rate epsilon := by
  unfold regularizedInnerRegularity regularInnerRate
  apply congrArg (fun rate : Nat -> Nat => CReal.Gmax rate (CReal.lv epsilon))
  funext precision
  exact innerLimitInnerRegularity_markov_self_rate_eq
    hw0 hw1 half cutoff observable (Q'.invSucc precision)

/-- Regularization preserves exact Markov-vacuum rate invariance. -/
theorem regularizedInnerRegularity_markov_vacuum_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (observable : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half observable)
        centralPhysicalLinearVacuum)).rate epsilon =
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          observable centralPhysicalLinearVacuum)).rate epsilon := by
  unfold regularizedInnerRegularity regularInnerRate
  apply congrArg (fun rate : Nat -> Nat => CReal.Gmax rate (CReal.lv epsilon))
  funext precision
  exact innerLimitInnerRegularity_markov_vacuum_rate_eq
    hw0 hw1 half cutoff observable (Q'.invSucc precision)

private theorem adaptive_input_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        ((centralPhysicalGraphAdaptiveReindexCauchy
          hw0 hw1 half X).seq stage)
        ((centralPhysicalGraphAdaptiveReindexCauchy
          hw0 hw1 half X).seq stage))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        ((centralPhysicalGraphAdaptiveReindexCauchy
          hw0 hw1 half X).seq stage)
        centralPhysicalLinearVacuum)).rate epsilon <= stage := by
  simpa only [centralPhysicalGraphAdaptiveReindexCauchy] using
    (centralPhysicalGraph_diagonal_admissible
      hw0 hw1 half X epsilon hepsilon stage hstage)

private theorem adaptive_action_self_rate_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          ((centralPhysicalGraphAdaptiveReindexCauchy
            hw0 hw1 half X).seq stage))
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          ((centralPhysicalGraphAdaptiveReindexCauchy
            hw0 hw1 half X).seq stage)))).rate epsilon <= stage := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  change (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Y.seq stage))
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Y.seq stage)))).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_self_rate_eq]
  exact (adaptive_input_rates_paid
    hw0 hw1 half X epsilon hepsilon stage hstage).1

private theorem adaptive_action_vacuum_rate_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          ((centralPhysicalGraphAdaptiveReindexCauchy
            hw0 hw1 half X).seq stage))
        centralPhysicalLinearVacuum)).rate epsilon <= stage := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  change (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Y.seq stage))
        centralPhysicalLinearVacuum)).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_vacuum_rate_eq]
  exact (adaptive_input_rates_paid
    hw0 hw1 half X epsilon hepsilon stage hstage).2

/-! ## 3. Four raw adaptive diagonal limits -/

theorem adaptiveInputSquare_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (Y.seq stage) (Y.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half Y Y) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  exact physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half Y Y
    (centralPhysicalGraphDiagonalRate hw0 hw1 half X)
    (fun epsilon hepsilon stage hstage =>
      (adaptive_input_rates_paid
        hw0 hw1 half X epsilon hepsilon stage hstage).1)

theorem adaptiveInputMean_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (Y.seq stage) centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half Y
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  simpa only [D, Y, SquaredSeminorm.constant] using
    (physicalCauchyPairingRegularizedDiagonal_converges
      hw0 hw1 half Y (D.constant centralPhysicalLinearVacuum)
      (centralPhysicalGraphDiagonalRate hw0 hw1 half X)
      (fun epsilon hepsilon stage hstage =>
        (adaptive_input_rates_paid
          hw0 hw1 half X epsilon hepsilon stage hstage).2))

theorem adaptiveActionSquare_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) (TY.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalLinearMarkovMapCauchy M Y
  exact physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half TY TY
    (centralPhysicalGraphDiagonalRate hw0 hw1 half X)
    (fun epsilon hepsilon stage hstage =>
      adaptive_action_self_rate_paid
        hw0 hw1 half X epsilon hepsilon stage hstage)

theorem adaptiveActionMean_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TY
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalLinearMarkovMapCauchy M Y
  simpa only [D, Y, TY, SquaredSeminorm.constant,
    centralPhysicalLinearMarkovMapCauchy] using
    (physicalCauchyPairingRegularizedDiagonal_converges
      hw0 hw1 half TY (D.constant centralPhysicalLinearVacuum)
      (centralPhysicalGraphDiagonalRate hw0 hw1 half X)
      (fun epsilon hepsilon stage hstage =>
        adaptive_action_vacuum_rate_paid
          hw0 hw1 half X epsilon hepsilon stage hstage))

/-! ## 4. Adaptive completed vacuum-pairing invariance -/

/-- Exact finite stationarity, now along the rate-admissible representative,
identifies the completed action and input vacuum pairings. -/
theorem adaptivePhysicalCauchyPairingLimit_markov_vacuum_equiv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TY
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      (physicalCauchyPairingLimit hw0 hw1 half Y
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalLinearMarkovMapCauchy M Y
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun stage => CReal.ofQ'
      ((innerLimit hw0 hw1 half
        (TY.seq stage) centralPhysicalLinearVacuum).approx stage))
    (bSeq := fun stage => CReal.ofQ'
      ((innerLimit hw0 hw1 half
        (Y.seq stage) centralPhysicalLinearVacuum).approx stage))
    (fun stage => CReal.ofQ'_equiv_of_eqv
      (innerLimit_markovCutoffAction_vacuum_approx_eqv
        hw0 hw1 half stage (Y.seq stage))) ?_ ?_
  · exact adaptiveActionMean_converges hw0 hw1 half M X
  · exact adaptiveInputMean_converges hw0 hw1 half X

/-- The completion modulus alone now supplies completed vacuum preservation:
adaptive normalization has discharged the former cofinality input. -/
def centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half M where
  pairing vector := by
    refine Quotient.inductionOn vector (fun X => ?_)
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    have hclass := centralPhysicalGraphAdaptiveReindex_class_eq
      hw0 hw1 half X
    rw [hclass]
    unfold centralPhysicalCutoffCompletedVacuum
      embedCentralPhysicalLinearObservable
    rw [centralPhysicalCutoffCompletedMarkovTransfer_mk]
    exact Quotient.sound
      (adaptivePhysicalCauchyPairingLimit_markov_vacuum_equiv
        hw0 hw1 half M X)

/-! ## 5. The two centered graph-norm limits -/

private theorem creal_mul_czero (value : CReal) :
    CReal.Equiv (CReal.mul value CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (value.approx n))

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by
      change (-(0 : Q')).eqv 0
      decide)

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (value.approx n)))

private theorem adaptive_completed_orthogonal_pairing_equiv_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid Y)) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half Y
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable at horthogonal
  change Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half Y
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) =
    CReal.RCzero at horthogonal
  exact Quotient.exact horthogonal

/-- Centered finite norms of the adaptive representative converge to its
completed squared norm. -/
theorem adaptiveInputCenteredNorm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageNorm hw0 hw1 half Y)
      (physicalCauchyPairingLimit hw0 hw1 half Y Y) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (Y.seq stage) (Y.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (Y.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half Y Y) := by
    simpa only [rawSeq, Y] using
      (adaptiveInputSquare_converges hw0 hw1 half X)
  have hmeanRaw := adaptiveInputMean_converges hw0 hw1 half X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq, Y] using hmeanRaw)
    exact adaptive_completed_orthogonal_pairing_equiv_zero Y horthogonal
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun stage => CReal.mul (meanSeq stage) (meanSeq stage))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun stage => CReal.add (rawSeq stage)
        (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
      (physicalCauchyPairingLimit hw0 hw1 half Y Y) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half Y Y))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageNorm_equiv_diagonal hw0 hw1 half Y stage)
  · simpa only [rawSeq, meanSeq] using hcenteredLimit

/-- Transferred centered finite norms of the adaptive representative converge
to the squared norm of its completed Markov image. -/
theorem adaptiveTransferredCenteredNorm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half Y)
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalLinearMarkovMapCauchy M Y
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TY.seq stage) (TY.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TY.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
    simpa only [rawSeq, Y, TY] using
      (adaptiveActionSquare_converges hw0 hw1 half M X)
  have hmeanRaw := adaptiveActionMean_converges hw0 hw1 half M X
  have hmeanTarget : CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TY
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero :=
    CReal.Equiv.trans
      (adaptivePhysicalCauchyPairingLimit_markov_vacuum_equiv
        hw0 hw1 half M X)
      (adaptive_completed_orthogonal_pairing_equiv_zero Y horthogonal)
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq, Y, TY] using hmeanRaw)
    exact hmeanTarget
  have hsquare := CReal.convergesTo_mul_general hmean hmean
  have hsquareZero : CReal.ConvergesTo
      (fun stage => CReal.mul (meanSeq stage) (meanSeq stage))
      CReal.czero :=
    CReal.convergesTo_limit_congr hsquare (creal_mul_czero CReal.czero)
  have hcenteredRaw := CReal.convergesTo_add hraw
    (CReal.convergesTo_neg hsquareZero)
  have hcenteredLimit : CReal.ConvergesTo
      (fun stage => CReal.add (rawSeq stage)
        (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
      (physicalCauchyPairingLimit hw0 hw1 half TY TY) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half TY TY))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageTransferredNorm_equiv_diagonal
        hw0 hw1 half M Y stage)
  · simpa only [rawSeq, meanSeq, TY] using hcenteredLimit

/-! ## 6. Contraction of the actual completed transfer -/

/-- The uniform finite sixteenth survives the adaptive centered graph-norm
limits at representative level. -/
theorem adaptiveRepresentative_operator_norm_gap_sixteenth
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal :
      let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
      CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid Y)) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalLinearMarkovMapCauchy M Y
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (CReal.mul
        (CReal.ofQ'
          (physicalCutoffSixteenth * physicalCutoffSixteenth))
        (physicalCauchyPairingLimit hw0 hw1 half Y Y)) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  apply CReal.leEv_of_convergesTo_le
    (adaptiveTransferredCenteredNorm_converges
      hw0 hw1 half M X horthogonal)
    (CReal.convergesTo_constMul
      (physicalCutoffSixteenth * physicalCutoffSixteenth)
      (adaptiveInputCenteredNorm_converges
        hw0 hw1 half X horthogonal))
  intro stage
  exact centralPhysicalCutoffCenteredStage_operator_norm_gap_sixteenth
    hw0 hw1 half certificate Y stage

/-- Adaptive normalization removes every graph-cofinality hypothesis.  The
completion modulus and finite fixed-nome sixteenth alone construct strict
contraction of the actual completed vacuum-complement transfer at `1/16`. -/
def centralPhysicalCutoffCompletedMarkovAdaptiveStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M
        (centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
          hw0 hw1 half M) where
  rate := physicalCutoffSixteenth
  rate_nonnegative := physicalCutoffSixteenth_nonnegative
  rate_lt_one := physicalCutoffSixteenth_lt_one
  contraction := by
    intro vector
    rcases vector with ⟨point, horthogonal⟩
    revert horthogonal
    refine Quotient.inductionOn point ?_
    intro X horthogonal
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    have hclass := centralPhysicalGraphAdaptiveReindex_class_eq
      hw0 hw1 half X
    have horthogonalY :
        CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
          (Quotient.mk
            (centralPhysicalCutoffLinearSquaredSeminorm
              hw0 hw1 half).completionSetoid Y) := by
      rw [← hclass]
      exact horthogonal
    let vectorY : CentralPhysicalCutoffCompletedVacuumComplement
        hw0 hw1 half :=
      ⟨Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid Y, horthogonalY⟩
    have hvector :
        (⟨Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid X, horthogonal⟩ :
          CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) =
        vectorY := by
      apply Subtype.ext
      exact hclass
    rw [hvector]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (centralPhysicalLinearMarkovMapCauchy M Y)
          (centralPhysicalLinearMarkovMapCauchy M Y)))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        (Quotient.mk CReal.crealSetoid
          (physicalCauchyPairingLimit hw0 hw1 half Y Y)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact adaptiveRepresentative_operator_norm_gap_sixteenth
      hw0 hw1 half M certificate X horthogonalY

/-! ## Axiom audit -/

#print axioms physicalCauchyPairingRegularizedDiagonal_converges
#print axioms regularizedInnerRegularity_markov_self_rate_eq
#print axioms regularizedInnerRegularity_markov_vacuum_rate_eq
#print axioms adaptiveInputSquare_converges
#print axioms adaptiveInputMean_converges
#print axioms adaptiveActionSquare_converges
#print axioms adaptiveActionMean_converges
#print axioms adaptivePhysicalCauchyPairingLimit_markov_vacuum_equiv
#print axioms centralPhysicalCutoffCompletedMarkovAdaptivePairingInvariant
#print axioms adaptiveInputCenteredNorm_converges
#print axioms adaptiveTransferredCenteredNorm_converges
#print axioms adaptiveRepresentative_operator_norm_gap_sixteenth
#print axioms centralPhysicalCutoffCompletedMarkovAdaptiveStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
