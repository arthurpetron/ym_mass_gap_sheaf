/-
# Vacuum-complement restriction of the adaptive completed BF4 transfer

The composed adaptive graph schedule pays the two input and two action inner
rates at every sufficiently late cutoff.  This file contracts those rate
witnesses with exact finite stationarity.

For a graph-normalized representative, let `Z` be its input-side adaptive
reindexing and `TZ` the actual adaptive Markov output.  Both vacuum-pairing
diagonals converge, and finite stationarity identifies their terms at every
cutoff.  Since `Z` represents the original completed point, the completed
adaptive transfer preserves pairing with the vacuum.

Consequently the transfer preserves the actual completed vacuum complement
and restricts to a rational-linear endomorphism there.  The historical
same-index completion modulus is not used.

## Axiom gate

Only explicit graph rates, exact finite stationarity, constructive limit
uniqueness, quotient descent, and the proved adaptive linearity laws are used.
There is no classical choice, noncomputable declaration, custom axiom, or
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerWellDefined
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The two vacuum-pairing graph limits -/

theorem centralPhysicalAdaptiveGraphInputMean_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (Z.seq stage) centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half Z
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  simpa only [D, Y, Z, SquaredSeminorm.constant] using
    (physicalCauchyPairingRegularizedDiagonal_converges
      hw0 hw1 half Z (D.constant centralPhysicalLinearVacuum)
      (centralPhysicalAdaptiveGraphDiagonalRate
        hw0 hw1 half pointwise X)
      (fun epsilon hepsilon stage hstage =>
        (centralPhysicalAdaptiveGraph_input_rates_paid
          hw0 hw1 half pointwise X epsilon hepsilon stage hstage).2))

theorem centralPhysicalAdaptiveGraphActionMean_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half TY
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  simpa only [D, Y, TY, SquaredSeminorm.constant] using
    (physicalCauchyPairingRegularizedDiagonal_converges
      hw0 hw1 half TY (D.constant centralPhysicalLinearVacuum)
      (centralPhysicalAdaptiveGraphDiagonalRate
        hw0 hw1 half pointwise X)
      (fun epsilon hepsilon stage hstage =>
        (centralPhysicalAdaptiveGraph_action_rates_paid
          hw0 hw1 half pointwise X epsilon hepsilon stage hstage).2))

/-! ## 2. Exact finite stationarity reaches the completed pairing -/

theorem centralPhysicalAdaptiveGraphPairingLimit_vacuum_equiv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TY
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      (physicalCauchyPairingLimit hw0 hw1 half Y
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
  let Z := centralPhysicalAdaptiveMarkovInputMapCauchy pointwise Y
  let TY := centralPhysicalAdaptiveMarkovMapCauchy pointwise Y
  have hdiagonal : CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TY
        (D.constant centralPhysicalLinearVacuum))
      (physicalCauchyPairingLimit hw0 hw1 half Z
        (D.constant centralPhysicalLinearVacuum)) := by
    refine CReal.Equiv_of_limit_of_equal
      (aSeq := fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (TY.seq stage) centralPhysicalLinearVacuum).approx stage))
      (bSeq := fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (Z.seq stage) centralPhysicalLinearVacuum).approx stage))
      (fun stage => CReal.ofQ'_equiv_of_eqv
        (innerLimit_markovCutoffAction_vacuum_approx_eqv
          hw0 hw1 half stage (Z.seq stage)))
      (centralPhysicalAdaptiveGraphActionMean_converges
        hw0 hw1 half pointwise X)
      (centralPhysicalAdaptiveGraphInputMean_converges
        hw0 hw1 half pointwise X)
  have hZY := physicalCauchyPairingLimit_welldef
    hw0 hw1 half
    (D.closeSymm (centralPhysicalAdaptiveMarkovInputMapClose pointwise Y))
    (D.closeRefl (D.constant centralPhysicalLinearVacuum))
  exact CReal.Equiv.trans hdiagonal hZY

/-! ## 3. Completed invariant and vacuum-complement endomorphism -/

structure CentralPhysicalAdaptiveCompletedMarkovVacuumPairingInvariant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData
      hw0 hw1 half) : Type where
  pairing : forall
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half),
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise vector)
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      centralPhysicalCutoffCompletedInner hw0 hw1 half vector
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)

def centralPhysicalAdaptiveCompletedMarkovPairingInvariant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData
      hw0 hw1 half) :
    CentralPhysicalAdaptiveCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half pointwise where
  pairing vector := by
    refine Quotient.inductionOn vector (fun X => ?_)
    let Y := centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X
    have hclass := centralPhysicalGraphAdaptiveReindex_class_eq
      hw0 hw1 half X
    rw [hclass]
    unfold centralPhysicalCutoffCompletedVacuum
      embedCentralPhysicalLinearObservable
    rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
    exact Quotient.sound
      (centralPhysicalAdaptiveGraphPairingLimit_vacuum_equiv
        hw0 hw1 half pointwise X)

theorem centralPhysicalAdaptiveCompletedMarkovTransfer_preserves_orthogonal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hvector : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise vector) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal at hvector ⊢
  rw [(centralPhysicalAdaptiveCompletedMarkovPairingInvariant
    hw0 hw1 half pointwise).pairing, hvector]

def centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun vector =>
    ⟨centralPhysicalAdaptiveCompletedMarkovTransfer pointwise vector.1,
      centralPhysicalAdaptiveCompletedMarkovTransfer_preserves_orthogonal
        pointwise vector.2⟩

theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer pointwise
        (centralPhysicalCutoffCompletedVacuumComplementZero hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuumComplementZero hw0 hw1 half := by
  apply Subtype.ext
  exact centralPhysicalAdaptiveCompletedMarkovTransfer_zero pointwise

theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_add
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (left right : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer pointwise
        (centralPhysicalCutoffCompletedVacuumComplementAdd
          hw0 hw1 half left right) =
      centralPhysicalCutoffCompletedVacuumComplementAdd hw0 hw1 half
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
          pointwise left)
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
          pointwise right) := by
  apply Subtype.ext
  exact centralPhysicalAdaptiveCompletedMarkovTransfer_add
    pointwise left.1 right.1

theorem centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_smul
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (scalar : Q')
    (vector : CentralPhysicalCutoffCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer pointwise
        (centralPhysicalCutoffCompletedVacuumComplementSmul
          hw0 hw1 half scalar vector) =
      centralPhysicalCutoffCompletedVacuumComplementSmul hw0 hw1 half scalar
        (centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
          pointwise vector) := by
  apply Subtype.ext
  exact centralPhysicalAdaptiveCompletedMarkovTransfer_smul
    pointwise scalar vector.1

def centralPhysicalAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedVacuumComplementQModule
        hw0 hw1 half) where
  toFun := centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
    pointwise
  map_zero :=
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_zero
      pointwise
  map_add :=
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_add
      pointwise
  map_smul :=
    centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer_smul
      pointwise

#print axioms centralPhysicalAdaptiveGraphPairingLimit_vacuum_equiv
#print axioms centralPhysicalAdaptiveCompletedMarkovPairingInvariant
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_preserves_orthogonal
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
#print axioms centralPhysicalAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
