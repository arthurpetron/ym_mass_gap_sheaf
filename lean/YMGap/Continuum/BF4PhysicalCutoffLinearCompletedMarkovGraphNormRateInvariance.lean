/-
# Markov syntax preserves the BF4 inner-regularity rates

The explicit inner modulus of an atomic physical cutoff-limit moment is the
uniform slab modulus; it does not inspect the atom value.  Addition and signed
scaling then propagate rates solely through the finite-linear syntax tree.
The recoded Markov action preserves that tree exactly, replacing only atomic
labels.

This file proves that the input and Markov-image pairing rates are therefore
identical.  The four-rate graph-norm cofinality residual contracts to two
input-side cofinality laws: self-pair and vacuum-pair.  No rate or analytic
certificate is inhabited here.

## Axiom gate

Only structural recursion on finite-linear syntax and equality rewriting are
used.  There is no classical choice, noncomputable declaration, custom axiom,
or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap

/-! ## 1. Exact invariance of the structural rates -/

private theorem atomLinearMarkovRate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (atomLinearInnerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).rate epsilon =
      (atomLinearInnerLimitInnerRegularity
        hw0 hw1 half left right).rate epsilon := by
  induction right generalizing epsilon with
  | zero => rfl
  | atom right => rfl
  | add first second hfirst hsecond =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        atomLinearInnerLimitInnerRegularity, CReal.InnerRegularity.add]
      rw [hfirst, hsecond]
  | smul scalar right hinduction =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        atomLinearInnerLimitInnerRegularity,
        CReal.InnerRegularity.scaleLeftSigned]
      rw [hinduction]

/-- Simultaneously recoding both arguments by the same finite-cutoff Markov
syntax leaves the explicit inner approximation rate exactly unchanged. -/
theorem innerLimitInnerRegularity_markov_both_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (innerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).rate epsilon =
      (innerLimitInnerRegularity hw0 hw1 half left right).rate epsilon := by
  induction left generalizing epsilon with
  | zero => rfl
  | atom left =>
      exact atomLinearMarkovRate_eq
        hw0 hw1 half cutoff left right epsilon
  | add first second hfirst hsecond =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.add]
      rw [hfirst, hsecond]
  | smul scalar left hinduction =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.scaleLeftSigned]
      rw [hinduction]

/-- In particular, the Markov-image self-pair rate is the input self-pair
rate, with no comparison loss. -/
theorem innerLimitInnerRegularity_markov_self_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (observable : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (innerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half observable)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half observable)).rate epsilon =
      (innerLimitInnerRegularity hw0 hw1 half
        observable observable).rate epsilon :=
  innerLimitInnerRegularity_markov_both_rate_eq
    hw0 hw1 half cutoff observable observable epsilon

/-- Pairing the recoded image with the unchanged atomic vacuum also has
exactly the input vacuum-pair rate. -/
theorem innerLimitInnerRegularity_markov_vacuum_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (observable : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (innerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half observable)
      centralPhysicalLinearVacuum).rate epsilon =
      (innerLimitInnerRegularity hw0 hw1 half
        observable centralPhysicalLinearVacuum).rate epsilon := by
  induction observable generalizing epsilon with
  | zero => rfl
  | atom observable =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        centralPhysicalLinearVacuum, innerLimitInnerRegularity,
        atomLinearInnerLimitInnerRegularity,
        atomInnerLimitInnerRegularity,
        centralPhysicalStationaryCutoffLimitInnerRegularity]
  | add first second hfirst hsecond =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.add]
      rw [hfirst, hsecond]
  | smul scalar observable hinduction =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.scaleLeftSigned]
      rw [hinduction]

/-! ## 2. The reduced two-rate residual -/

/-- Only two input-side rates are needed: self-pair and vacuum-pair.  Exact
Markov syntax invariance constructs both corresponding action-side rates. -/
structure CentralPhysicalLinearGraphNormInputInnerCofinality
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  stageRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat
  inputSelfRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, stageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq stage) (X.seq stage)).rate epsilon <= stage
  inputVacuumRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, stageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).rate epsilon <= stage

namespace CentralPhysicalLinearGraphNormInputInnerCofinality

/-- Exact rate invariance supplies the previously separate two-field vacuum
cofinality record. -/
def toVacuumPairingInnerCofinality
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearGraphNormInputInnerCofinality
      hw0 hw1 half) :
    CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
      hw0 hw1 half where
  stageRate := cofinality.stageRate
  inputRate_le_stage := cofinality.inputVacuumRate_le_stage
  actionRate_le_stage := by
    intro X epsilon hepsilon stage hstage
    rw [innerLimitInnerRegularity_markov_vacuum_rate_eq]
    exact cofinality.inputVacuumRate_le_stage
      X epsilon hepsilon stage hstage

/-- The same two input rates construct all four graph-norm cofinality rates. -/
def toGraphNormInnerCofinality
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearGraphNormInputInnerCofinality
      hw0 hw1 half) :
    CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half where
  vacuum := cofinality.toVacuumPairingInnerCofinality
  selfStageRate := cofinality.stageRate
  inputSelfRate_le_stage := cofinality.inputSelfRate_le_stage
  actionSelfRate_le_stage := by
    intro X epsilon hepsilon stage hstage
    rw [innerLimitInnerRegularity_markov_self_rate_eq]
    exact cofinality.inputSelfRate_le_stage
      X epsilon hepsilon stage hstage

/-- The reduced two-rate datum therefore constructs the completed transfer's
two centered graph-norm convergence laws. -/
def toCenteredGraphNormConvergence
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearGraphNormInputInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :=
  cofinality.toGraphNormInnerCofinality.toCenteredGraphNormConvergence M

/-- Thus the completion modulus, two input-side cofinal rates, and the finite
fixed-nome sixteenth suffice for strict contraction of the actual completed
vacuum-complement transfer at `1/16`. -/
def toStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearGraphNormInputInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M
        cofinality.toVacuumPairingInnerCofinality.toPairingInvariant :=
  cofinality.toGraphNormInnerCofinality.toStrictContractionData M certificate

end CentralPhysicalLinearGraphNormInputInnerCofinality

/-! ## Axiom audit -/

#print axioms innerLimitInnerRegularity_markov_both_rate_eq
#print axioms innerLimitInnerRegularity_markov_self_rate_eq
#print axioms innerLimitInnerRegularity_markov_vacuum_rate_eq
#print axioms CentralPhysicalLinearGraphNormInputInnerCofinality
#print axioms CentralPhysicalLinearGraphNormInputInnerCofinality.toVacuumPairingInnerCofinality
#print axioms CentralPhysicalLinearGraphNormInputInnerCofinality.toGraphNormInnerCofinality
#print axioms CentralPhysicalLinearGraphNormInputInnerCofinality.toCenteredGraphNormConvergence
#print axioms CentralPhysicalLinearGraphNormInputInnerCofinality.toStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
