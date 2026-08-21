/-
# Graph-admissible schedule for the adaptive completed BF4 transfer

The adaptive Markov sampler pays cross-cutoff and selected-to-anchor distance
rates, while the earlier graph sampler pays self-pair and vacuum-pair inner
rates.  This file composes the two constructive schedules.

First graph-normalize an arbitrary completion representative.  Then feed that
representative to the adaptive Markov sampler.  Cofinality of the second
sampler puts every selected input index beyond the graph rate requested at the
current tolerance.  Since the selected index never exceeds the action cutoff,
both input graph rates, and by exact syntax-rate invariance both action graph
rates, are paid by the current cutoff.

This is the rate-theoretic bridge needed for vacuum-pairing and graph-norm
limits of the new adaptive transfer.  It requires only pointwise dense
cross-cutoff data, not the historical same-index completion modulus.

## Axiom gate

Only executable slow diagonals, explicit Cauchy moduli, inner-rate
regularization, and quotient soundness are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The input-side adaptive reindexing -/

/-- Sample only the input representative along the indices selected for the
adaptive Markov diagonal. -/
def centralPhysicalAdaptiveMarkovInputMapCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := X.seq (centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X stage)
  modulus epsilon := centralPhysicalAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise X (X.modulus epsilon)
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    exact X.isCauchy epsilon hepsilon
      (centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X first)
      (centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X second)
      (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
        hw0 hw1 half pointwise X (X.modulus epsilon) first hfirst)
      (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
        hw0 hw1 half pointwise X (X.modulus epsilon) second hsecond)

/-- Input-side adaptive sampling remains explicitly close to the original
completion representative. -/
def centralPhysicalAdaptiveMarkovInputMapClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalAdaptiveMarkovInputMapCauchy pointwise X) where
  modulus epsilon := max (X.modulus epsilon)
    (centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X (X.modulus epsilon))
  close := by
    intro epsilon hepsilon stage hstage
    have hraw : X.modulus epsilon <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hsample : centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise X (X.modulus epsilon) <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    exact X.isCauchy epsilon hepsilon stage
      (centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X stage)
      hraw
      (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
        hw0 hw1 half pointwise X (X.modulus epsilon) stage hsample)

theorem centralPhysicalAdaptiveMarkovInputMap_class_eq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalAdaptiveMarkovInputMapCauchy pointwise X) :=
  Quotient.sound ⟨centralPhysicalAdaptiveMarkovInputMapClose pointwise X⟩

/-! ## 2. Composition with the graph-normalized representative -/

def centralPhysicalAdaptiveGraphDiagonalRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let graphThreshold := centralPhysicalGraphDiagonalRate
    hw0 hw1 half X epsilon
  centralPhysicalAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise Y
      (max graphThreshold
        (max (CReal.lv epsilon) (CReal.lv epsilon)))

private theorem centralPhysicalAdaptiveMarkovSampleIndex_le_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X stage <= stage := by
  exact greatestAdmissibleAux_le
    (centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X) stage stage

/-- The composed sampler pays both graph rates of its selected input term at
the current action cutoff. -/
theorem centralPhysicalAdaptiveGraph_input_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalAdaptiveGraphDiagonalRate
      hw0 hw1 half pointwise X epsilon <= stage) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (Z.seq stage) (Z.seq stage))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (Z.seq stage) centralPhysicalLinearVacuum)).rate epsilon <= stage := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let graphThreshold := centralPhysicalGraphDiagonalRate
    hw0 hw1 half X epsilon
  let index := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise Y stage
  have hpaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise Y graphThreshold epsilon epsilon
    hepsilon hepsilon stage hstage
  have hgraph := centralPhysicalGraph_diagonal_admissible
    hw0 hw1 half X epsilon hepsilon index hpaid.1
  have hindexStage : index <= stage :=
    centralPhysicalAdaptiveMarkovSampleIndex_le_stage
      hw0 hw1 half pointwise Y stage
  exact ⟨Nat.le_trans hgraph.1 hindexStage,
    Nat.le_trans hgraph.2 hindexStage⟩

/-! ## 3. Exact rate invariance pays both action graph rates -/

private theorem regularized_markov_self_rate_eq
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

private theorem regularized_markov_vacuum_rate_eq
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

theorem centralPhysicalAdaptiveGraph_action_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalAdaptiveGraphDiagonalRate
      hw0 hw1 half pointwise X epsilon <= stage) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (TY.seq stage) (TY.seq stage))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (TY.seq stage) centralPhysicalLinearVacuum)).rate epsilon <= stage := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have hinput := centralPhysicalAdaptiveGraph_input_rates_paid
    hw0 hw1 half pointwise X epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Z.seq stage))
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Z.seq stage)))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (Z.seq stage))
        centralPhysicalLinearVacuum)).rate epsilon <= stage
  rw [regularized_markov_self_rate_eq,
    regularized_markov_vacuum_rate_eq]
  exact hinput

#print axioms centralPhysicalAdaptiveMarkovInputMapCauchy
#print axioms centralPhysicalAdaptiveMarkovInputMapClose
#print axioms centralPhysicalAdaptiveMarkovInputMap_class_eq
#print axioms centralPhysicalAdaptiveGraph_input_rates_paid
#print axioms centralPhysicalAdaptiveGraph_action_rates_paid

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
