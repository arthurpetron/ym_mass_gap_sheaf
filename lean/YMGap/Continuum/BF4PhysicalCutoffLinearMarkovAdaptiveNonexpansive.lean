/-
# Norm nonexpansiveness of the adaptive completed BF4 transfer

The adaptive graph schedule gives, for every cutoff-completion
representative, an input diagonal and its literal same-cutoff Markov image.
Both squared-norm streams converge to the corresponding completed pairings.
At every finite stage, exact physical `L2` contraction compares those two
streams.  Passing that inequality through their constructive-real limits
proves that the actual adaptive completed transfer is norm-nonexpansive on
the whole cutoff-completed carrier.

This is a continuity theorem with rate one.  It does not supply a common
strict rate below one, a thermodynamic limit, a continuum QFT, or the Clay
mass-gap conclusion.

## Axiom gate

Only the finite rational Markov contraction, explicit adaptive graph rates,
constructive-real limit order, and quotient soundness are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveNonexpansive

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovL2Contraction
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The finite inequality on the aligned adaptive graph diagonal -/

/-- At one adaptive graph stage, the literal Markov-image diagonal is bounded
by its aligned input diagonal. -/
theorem centralPhysicalAdaptiveGraph_stage_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    (innerLimit hw0 hw1 half
      (TY.seq stage) (TY.seq stage)).approx stage <=
      (innerLimit hw0 hw1 half
        (Z.seq stage) (Z.seq stage)).approx stage := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have houtput := innerLimit_markovCutoffAction_both_approx_eqv
    hw0 hw1 half stage (Z.seq stage) (Z.seq stage)
  have hinput := innerLimit_approx_eqv_stage
    hw0 hw1 half stage (Z.seq stage) (Z.seq stage)
  have hfinite := centralPhysicalMarkovApply_l2_contraction
    w (Q'.le_of_lt hw0) stage half (Z.seq stage).value
  change
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half (Z.seq stage))
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half (Z.seq stage))).approx stage <=
      (innerLimit hw0 hw1 half
        (Z.seq stage) (Z.seq stage)).approx stage
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv houtput)
    (Q'.le_trans' _ _ _ hfinite (Q'.ge_of_eqv hinput))

/-! ## 2. Representative and completed norm nonexpansiveness -/

/-- The finite stage inequalities survive the two adaptive graph-square
limits for every completion representative. -/
theorem centralPhysicalAdaptiveGraph_pairing_nonexpansive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.leEv
      (physicalCauchyPairingLimit hw0 hw1 half TY TY)
      (physicalCauchyPairingLimit hw0 hw1 half Z Z) := by
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalAdaptiveGraphActionSquare_converges
      hw0 hw1 half pointwise X)
    (centralPhysicalAdaptiveGraphInputSquare_converges
      hw0 hw1 half pointwise X)
  intro stage
  exact CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ'
      (centralPhysicalAdaptiveGraph_stage_square_le
        hw0 hw1 half pointwise X stage))

/-- The actual adaptive completed Markov transfer is norm-nonexpansive on the
whole fixed-nome, fixed-volume cutoff completion. -/
theorem centralPhysicalAdaptiveCompletedMarkovTransfer_norm_nonexpansive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise vector)
        (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise vector))
      (centralPhysicalCutoffCompletedInner hw0 hw1 half vector vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have hXY := centralPhysicalGraphAdaptiveReindex_class_eq
    hw0 hw1 half X
  have hYZ := centralPhysicalAdaptiveMarkovInputMap_class_eq pointwise Y
  rw [hXY]
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
  rw [hYZ]
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half TY TY))
    (Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half Z Z))
  rw [CReal.RCle_mk]
  exact centralPhysicalAdaptiveGraph_pairing_nonexpansive
    hw0 hw1 half pointwise X

#print axioms centralPhysicalAdaptiveGraph_stage_square_le
#print axioms centralPhysicalAdaptiveGraph_pairing_nonexpansive
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_norm_nonexpansive

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveNonexpansive
