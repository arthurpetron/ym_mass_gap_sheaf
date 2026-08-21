/-
# Diagonal finite-to-completed vacuum-pairing invariance

Finite physical BF4 stationarity already says that the genuine cutoff Markov
action preserves pairing with the constant vacuum.  The same-syntax recoding
therefore gives an exact equality when both limiting inner forms are evaluated
at that same finite cutoff.

The completed form, however, first removes the representation cutoff inside
each dense pairing and then takes an outer Cauchy-representative limit.  The
finite diagonal equality reaches that iterated limit only when the diagonal
cutoff eventually dominates the explicit inner-regularity rates of both
pairings.  This file isolates exactly that cofinality requirement as
`Type`-level data, proves that it yields eventual two-sided closeness, and then
constructs the completed vacuum-pairing invariant and the already-factored
vacuum-complement transfer.

No inhabitant of the cofinal inner-regularity data is claimed.  In particular,
finite stationarity alone is not misreported as completed stationarity.

## Axiom gate

Only exact finite stationarity, explicit constructive-real regularity rates,
constructive limit uniqueness, and the proved quotient descents are used.
There is no classical choice, noncomputable declaration, custom axiom, or
unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite diagonal vacuum pairing -/

private theorem centralPhysicalWeightedInner_linearVacuum_right
    (w : Q') (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling -> Q') :
    centralPhysicalWeightedInner w hw cutoff half observable
        centralPhysicalLinearVacuum.value ≈
      centralPhysicalStationaryMean w hw cutoff half observable := by
  change centralPhysicalWeightedInner w hw cutoff half observable
      (fun _ => 1) ≈
    centralPhysicalStationaryMean w hw cutoff half observable
  unfold centralPhysicalWeightedInner centralPhysicalStationaryMean
  apply listQSum_congr
  intro state
  exact Q'.mul_eqv_congr_left
    (centralPhysicalRowMarginal w hw cutoff half state) _ _
    (Q'.mul_one_eqv (observable state))

/-- At every matched cutoff, finite stationarity makes the approximation of
`<P_cutoff x, vacuum>` exactly equal to the approximation of
`<x, vacuum>`.  This is unconditional finite-cutoff input to the later
cofinality bridge. -/
theorem innerLimit_markovCutoffAction_vacuum_approx_eqv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (observable : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half observable)
      centralPhysicalLinearVacuum).approx cutoff ≈
      (innerLimit hw0 hw1 half
        observable centralPhysicalLinearVacuum).approx cutoff := by
  have haction := innerLimit_approx_eqv_stage hw0 hw1 half cutoff
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half observable)
    centralPhysicalLinearVacuum
  have hinput := innerLimit_approx_eqv_stage hw0 hw1 half cutoff
    observable centralPhysicalLinearVacuum
  rw [centralPhysicalSmulGNS_B_eq] at haction hinput
  have hrecodedMean :
      centralPhysicalStationaryMean w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) cutoff half observable).value ≈
        centralPhysicalStationaryMean w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) cutoff half
            observable.value) := by
    unfold centralPhysicalStationaryMean
    apply listQSum_congr_on
    intro source hsource
    exact Q'.mul_eqv_congr_left
      (centralPhysicalRowMarginal
        w (Q'.le_of_lt hw0) cutoff half source) _ _
      (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (Q'.le_of_lt hw0) cutoff half observable source hsource)
  exact Q'.eqv_trans _ _ _ haction
    (Q'.eqv_trans _ _ _
      (centralPhysicalWeightedInner_linearVacuum_right
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half observable).value)
      (Q'.eqv_trans _ _ _ hrecodedMean
        (Q'.eqv_trans _ _ _
          (centralPhysicalStationaryMean_markovApply
            w (Q'.le_of_lt hw0) cutoff half observable.value)
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (centralPhysicalWeightedInner_linearVacuum_right
                w (Q'.le_of_lt hw0) cutoff half observable.value))
            (Q'.eqv_symm hinput)))))

/-! ## 2. The exact diagonal cofinality residual -/

/-- The missing cofinality statement between the outer representative stage
and the inner representation-cutoff regularity.

For every input Cauchy representative and tolerance, a stage rate is supplied
after which the diagonal stage dominates the explicit inner-regularity rate
both for `<P_n X_n, vacuum>` and for `<X_n, vacuum>`. -/
structure CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  stageRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat
  actionRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, stageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))
        centralPhysicalLinearVacuum).rate epsilon <= stage
  inputRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, stageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).rate epsilon <= stage

/-- Explicit eventual two-sided approximation closeness of the two dense
vacuum-pairing sequences.  Both the outer-stage and inner-approximation rates
remain recoverable data. -/
structure CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  stageRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat
  approxRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat -> Nat
  close : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, stageRate X epsilon <= stage ->
    forall k, approxRate X epsilon stage <= k ->
      (innerLimit hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))
        centralPhysicalLinearVacuum).approx k <=
          (innerLimit hw0 hw1 half
            (X.seq stage) centralPhysicalLinearVacuum).approx k + epsilon /\
      (innerLimit hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).approx k <=
          (innerLimit hw0 hw1 half
            (centralPhysicalLinearMarkovCutoffAction
              (Q'.le_of_lt hw0) stage half (X.seq stage))
            centralPhysicalLinearVacuum).approx k + epsilon

/-- Exact finite stationarity turns inner-rate cofinality into eventual
two-sided closeness of the dense vacuum-pairing sequences. -/
def CentralPhysicalLinearMarkovVacuumPairingInnerCofinality.toDiagonalControl
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
      hw0 hw1 half) :
    CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
      hw0 hw1 half where
  stageRate X epsilon :=
    cofinality.stageRate X (HalfPow.half * epsilon)
  approxRate _ _ stage := stage
  close := by
    intro X epsilon hepsilon stage hstage k hk
    let q := HalfPow.half * epsilon
    have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
    let actionPair := innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half (X.seq stage))
      centralPhysicalLinearVacuum
    let inputPair := innerLimit hw0 hw1 half
      (X.seq stage) centralPhysicalLinearVacuum
    have hactionRate := cofinality.actionRate_le_stage
      X q hq stage hstage
    have hinputRate := cofinality.inputRate_le_stage
      X q hq stage hstage
    have haction :=
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))
        centralPhysicalLinearVacuum).regular
          q hq stage k hactionRate (Nat.le_trans hactionRate hk)
    have hinput :=
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).regular
          q hq stage k hinputRate (Nat.le_trans hinputRate hk)
    have hfinite := innerLimit_markovCutoffAction_vacuum_approx_eqv
      hw0 hw1 half stage (X.seq stage)
    have htwo : (q + q) ≈ epsilon := ExpNeg.two_halves epsilon
    constructor
    · have h1 : actionPair.approx k <= inputPair.approx stage + q :=
        Q'.le_trans' _ _ _ haction.2
          (Q'.add_le_add_right _ _ q (Q'.le_of_eqv hfinite))
      have h2 : actionPair.approx k <=
          (inputPair.approx k + q) + q :=
        Q'.le_trans' _ _ _ h1
          (Q'.add_le_add_right _ _ q hinput.1)
      exact Q'.le_trans' _ _ _ h2
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.add_assoc_eqv (inputPair.approx k) q q)
            (Q'.add_eqv_congr_left
              (inputPair.approx k) (q + q) epsilon htwo)))
    · have h1 : inputPair.approx k <= actionPair.approx stage + q :=
        Q'.le_trans' _ _ _ hinput.2
          (Q'.add_le_add_right _ _ q
            (Q'.le_of_eqv (Q'.eqv_symm hfinite)))
      have h2 : inputPair.approx k <=
          (actionPair.approx k + q) + q :=
        Q'.le_trans' _ _ _ h1
          (Q'.add_le_add_right _ _ q haction.1)
      exact Q'.le_trans' _ _ _ h2
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.add_assoc_eqv (actionPair.approx k) q q)
            (Q'.add_eqv_congr_left
              (actionPair.approx k) (q + q) epsilon htwo)))

/-! ## 3. Contracting diagonal control to completed pairing invariance -/

private theorem convergesTo_of_vacuumPairingDiagonalControl
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (control : CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
      hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => innerLimit hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))
        centralPhysicalLinearVacuum)
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have hinput := physicalCauchyPairingSeq_converges hw0 hw1 half X
    ((centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).constant centralPhysicalLinearVacuum)
  obtain ⟨inputStage, hinputStage⟩ := hinput q hq
  refine ⟨max inputStage (control.stageRate X q),
    fun stage hstage => ?_⟩
  have hinputStage' : inputStage <= stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hcontrolStage : control.stageRate X q <= stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  obtain ⟨inputApprox, hinputApprox⟩ :=
    hinputStage stage hinputStage'
  refine ⟨max inputApprox (control.approxRate X q stage),
    fun k hk => ?_⟩
  have hkInput : inputApprox <= k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hkControl : control.approxRate X q stage <= k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hinputForward, hinputBackward⟩ :=
    hinputApprox k hkInput
  obtain ⟨hactionInput, hinputAction⟩ :=
    control.close X q hq stage hcontrolStage k hkControl
  have htwo : (q + q) ≈ epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain := Q'.le_trans' _ _ _ hactionInput
      (Q'.add_le_add_right _ _ q hinputForward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))
  · have hchain := Q'.le_trans' _ _ _ hinputBackward
      (Q'.add_le_add_right _ _ q hinputAction)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))

/-- Diagonal pairing control identifies the two representative-level outer
pairing limits. -/
theorem physicalCauchyPairingLimit_markov_vacuum_equiv
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (control : CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
      hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  let vacuumRep := (centralPhysicalCutoffLinearSquaredSeminorm
    hw0 hw1 half).constant centralPhysicalLinearVacuum
  let actionRep := centralPhysicalLinearMarkovMapCauchy M X
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half actionRep vacuumRep)
    (bSeq := physicalCauchyPairingSeq hw0 hw1 half actionRep vacuumRep)
    (fun _ => CReal.Equiv.refl _)
    (physicalCauchyPairingSeq_converges
      hw0 hw1 half actionRep vacuumRep)
  exact convergesTo_of_vacuumPairingDiagonalControl control X

/-- The concrete diagonal control constructs the minimum completed
vacuum-pairing invariant required by the vacuum-complement restriction. -/
def CentralPhysicalLinearMarkovVacuumPairingDiagonalControl.toPairingInvariant
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    (control : CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
      hw0 hw1 half) :
    CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half M where
  pairing vector := by
    refine Quotient.inductionOn vector (fun X => ?_)
    unfold centralPhysicalCutoffCompletedVacuum
      embedCentralPhysicalLinearObservable
    rw [centralPhysicalCutoffCompletedMarkovTransfer_mk]
    exact Quotient.sound
      (physicalCauchyPairingLimit_markov_vacuum_equiv M control X)

/-- The smaller cofinal inner-regularity datum therefore constructs the
minimum completed pairing invariant. -/
def CentralPhysicalLinearMarkovVacuumPairingInnerCofinality.toPairingInvariant
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half}
    (cofinality : CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
      hw0 hw1 half) :
    CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half M :=
  cofinality.toDiagonalControl.toPairingInvariant

/-- The completion modulus plus diagonal inner-rate cofinality contract all
the way to a rational-linear endomorphism of the concrete completed vacuum
complement. -/
def centralPhysicalCutoffCompletedVacuumComplementMarkovOfCofinality
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (cofinality : CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
      hw0 hw1 half) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedVacuumComplementQModule
        hw0 hw1 half) :=
  centralPhysicalCutoffCompletedVacuumComplementMarkovQLinearEndomorphism
    M cofinality.toPairingInvariant

/-! ## Axiom audit -/

#print axioms innerLimit_markovCutoffAction_vacuum_approx_eqv
#print axioms CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
#print axioms CentralPhysicalLinearMarkovVacuumPairingDiagonalControl
#print axioms CentralPhysicalLinearMarkovVacuumPairingInnerCofinality.toDiagonalControl
#print axioms physicalCauchyPairingLimit_markov_vacuum_equiv
#print axioms CentralPhysicalLinearMarkovVacuumPairingDiagonalControl.toPairingInvariant
#print axioms CentralPhysicalLinearMarkovVacuumPairingInnerCofinality.toPairingInvariant
#print axioms centralPhysicalCutoffCompletedVacuumComplementMarkovOfCofinality

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
