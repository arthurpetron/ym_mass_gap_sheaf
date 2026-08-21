/-
# Inner-rate cofinality compiles to the completed BF4 graph norm

The finite completed sixteenth and the cutoff-removed completed transfer are
already concrete.  Their remaining graph-norm bridge asks that four diagonal
inner approximations be late enough at their own outer cutoff: the input and
transferred self-pairings, and the corresponding vacuum pairings.

The vacuum-pairing frontier already names the two vacuum controls.  This file
adds only the two self-pair controls, proves a reusable diagonal convergence
lemma, and compiles those four explicit rates into both centered graph-norm
convergence laws.  Consequently the prior graph-norm compiler yields the
same-object strict contraction at `1/16` once the finite sixteenth is supplied.

No cofinality datum, completion modulus, or finite sixteenth certificate is
inhabited here.

## Axiom gate

Only explicit natural-number rates, exact finite centering and stationarity,
constructive-real limit algebra, and quotient exactness are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
import YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Diagonalizing one outer pairing limit -/

/-- If the outer stage eventually dominates the explicit inner approximation
rate of its own pairing, the diagonal rational approximations converge to the
already constructed outer pairing limit. -/
theorem physicalCauchyPairingDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stageRate : Q' -> Nat)
    (rate_le_stage : forall
      (epsilon : Q'), (0 : Q') < epsilon ->
      forall stage, stageRate epsilon <= stage ->
        (innerLimitInnerRegularity hw0 hw1 half
          (X.seq stage) (Y.seq stage)).rate epsilon <= stage) :
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
  let innerRate := (innerLimitInnerRegularity hw0 hw1 half
    (X.seq stage) (Y.seq stage)).rate q
  have hinnerRate : innerRate <= stage :=
    rate_le_stage q hq stage hrateStage
  obtain ⟨outerApprox, houterApprox⟩ := houterStage stage houter
  refine ⟨max outerApprox innerRate, fun k hk => ?_⟩
  have hkOuter : outerApprox <= k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hkInner : innerRate <= k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hinnerForward, hinnerBackward⟩ :=
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq stage) (Y.seq stage)).regular
        q hq stage k hinnerRate hkInner
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

/-! ## 2. The two genuinely new self-pair cofinality laws -/

/-- The graph-norm residual after reusing the already isolated vacuum-pairing
cofinality.  Its only new content is diagonal cofinality for the input and
Markov-image self-pairings. -/
structure CentralPhysicalLinearMarkovGraphNormInnerCofinality
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  vacuum : CentralPhysicalLinearMarkovVacuumPairingInnerCofinality
    hw0 hw1 half
  selfStageRate :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy -> Q' -> Nat
  inputSelfRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, selfStageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq stage) (X.seq stage)).rate epsilon <= stage
  actionSelfRate_le_stage : forall
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall stage, selfStageRate X epsilon <= stage ->
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half (X.seq stage))).rate epsilon <= stage

namespace CentralPhysicalLinearMarkovGraphNormInnerCofinality

/-! ## 3. Raw diagonal square and mean limits -/

theorem inputSquare_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (X.seq stage) (X.seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half X X) :=
  physicalCauchyPairingDiagonal_converges hw0 hw1 half X X
    (cofinality.selfStageRate X)
    (cofinality.inputSelfRate_le_stage X)

theorem inputMean_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (X.seq stage) centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) :=
  physicalCauchyPairingDiagonal_converges hw0 hw1 half X
    ((centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).constant centralPhysicalLinearVacuum)
    (cofinality.vacuum.stageRate X)
    (cofinality.vacuum.inputRate_le_stage X)

theorem actionSquare_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
          ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        (centralPhysicalLinearMarkovMapCauchy M X)) :=
  physicalCauchyPairingDiagonal_converges hw0 hw1 half
    (centralPhysicalLinearMarkovMapCauchy M X)
    (centralPhysicalLinearMarkovMapCauchy M X)
    (cofinality.selfStageRate X)
    (cofinality.actionSelfRate_le_stage X)

theorem actionMean_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
          centralPhysicalLinearVacuum).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) :=
  physicalCauchyPairingDiagonal_converges hw0 hw1 half
    (centralPhysicalLinearMarkovMapCauchy M X)
    ((centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).constant centralPhysicalLinearVacuum)
    (cofinality.vacuum.stageRate X)
    (cofinality.vacuum.actionRate_le_stage X)

/-! ## 4. Exact finite centering identities for the two diagonal streams -/

private theorem qmul_eqv_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem creal_ofQ'_centered_equiv (raw mean : Q') :
    CReal.Equiv
      (CReal.ofQ' (raw + -(mean * mean)))
      (CReal.add (CReal.ofQ' raw)
        (CReal.neg (CReal.mul (CReal.ofQ' mean) (CReal.ofQ' mean)))) :=
  YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl _)

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

private theorem completed_orthogonal_pairing_equiv_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable at horthogonal
  change Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) =
    CReal.RCzero at horthogonal
  exact Quotient.exact horthogonal

/-- Exact finite centering identifies the literal input stage norm with the
raw diagonal self-pair minus the square of the raw diagonal vacuum pairing. -/
theorem centeredStageNorm_equiv_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CReal.Equiv
      (centralPhysicalCutoffCenteredStageNorm hw0 hw1 half X stage)
      (CReal.add
        (CReal.ofQ'
          ((innerLimit hw0 hw1 half
            (X.seq stage) (X.seq stage)).approx stage))
        (CReal.neg
          (CReal.mul
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half
                (X.seq stage) centralPhysicalLinearVacuum).approx stage))
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half
                (X.seq stage) centralPhysicalLinearVacuum).approx stage))))) := by
  let hw := Q'.le_of_lt hw0
  let D := (centralPhysicalSmulGNS w hw stage half).toGNSData
  let raw := (X.seq stage).value
  let mean := centralPhysicalStationaryMean w hw stage half raw
  let centered := centralPhysicalCenteredObservable w hw stage half raw
  have hcentered : D.B centered centered ≈
      D.B raw raw + -(mean * mean) := by
    simpa only [D, raw, mean, centered, centralPhysicalSmulGNS_B_eq] using
      (centralPhysicalCenteredObservable_norm_identity
        w hw stage half raw)
  have hraw := innerLimit_approx_eqv_stage
    hw0 hw1 half stage (X.seq stage) (X.seq stage)
  have hmeanStage := innerLimit_approx_eqv_stage
    hw0 hw1 half stage (X.seq stage) centralPhysicalLinearVacuum
  have hmean :
      (innerLimit hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).approx stage ≈ mean := by
    exact Q'.eqv_trans _ _ _ hmeanStage
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (centralPhysicalSmulGNS_B_eq
            w hw stage half raw centralPhysicalLinearVacuum.value))
        (centralPhysicalWeightedInner_vacuum_right
          w hw stage half raw))
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro k
  change D.B centered centered ≈
    (innerLimit hw0 hw1 half
        (X.seq stage) (X.seq stage)).approx stage +
      -((innerLimit hw0 hw1 half
          (X.seq stage) centralPhysicalLinearVacuum).approx stage *
        (innerLimit hw0 hw1 half
          (X.seq stage) centralPhysicalLinearVacuum).approx stage)
  exact Q'.eqv_trans _ _ _ hcentered
    (Q'.add_eqv_congr'
      (Q'.eqv_symm hraw)
      (Q'.neg_eqv_congr _ _
        (qmul_eqv_congr (Q'.eqv_symm hmean) (Q'.eqv_symm hmean))))

/-- Exact finite stationarity and centered Markov intertwining identify the
literal transferred stage norm with the Markov-image diagonal self-pair minus
the square of its diagonal vacuum pairing. -/
theorem centeredStageTransferredNorm_equiv_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CReal.Equiv
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X stage)
      (CReal.add
        (CReal.ofQ'
          ((innerLimit hw0 hw1 half
            ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
            ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)).approx stage))
        (CReal.neg
          (CReal.mul
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half
                ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
                centralPhysicalLinearVacuum).approx stage))
            (CReal.ofQ'
              ((innerLimit hw0 hw1 half
                ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
                centralPhysicalLinearVacuum).approx stage))))) := by
  let hw := Q'.le_of_lt hw0
  let D := (centralPhysicalSmulGNS w hw stage half).toGNSData
  let raw := (X.seq stage).value
  let transferred := centralPhysicalMarkovApply w hw stage half raw
  let mean := centralPhysicalStationaryMean w hw stage half transferred
  let centered := centralPhysicalCenteredObservable w hw stage half raw
  let centeredTransferred :=
    centralPhysicalCenteredObservable w hw stage half transferred
  have hintertwine : D.rad
      (centralPhysicalMarkovApply w hw stage half centered)
      centeredTransferred :=
    centralPhysicalMarkovApply_centered_rad w hw stage half raw
  have hwelldef :
      D.B (centralPhysicalMarkovApply w hw stage half centered)
          (centralPhysicalMarkovApply w hw stage half centered) ≈
        D.B centeredTransferred centeredTransferred :=
    D.B_welldef hintertwine hintertwine
  have hcentered : D.B centeredTransferred centeredTransferred ≈
      D.B transferred transferred + -(mean * mean) := by
    simpa only [D, transferred, mean, centeredTransferred,
      centralPhysicalSmulGNS_B_eq] using
      (centralPhysicalCenteredObservable_norm_identity
        w hw stage half transferred)
  have hraw := innerLimit_markovCutoffAction_both_approx_eqv
    hw0 hw1 half stage (X.seq stage) (X.seq stage)
  have hinputMeanStage := innerLimit_approx_eqv_stage
    hw0 hw1 half stage (X.seq stage) centralPhysicalLinearVacuum
  have hinputMean :
      (innerLimit hw0 hw1 half
        (X.seq stage) centralPhysicalLinearVacuum).approx stage ≈
        centralPhysicalStationaryMean w hw stage half raw := by
    exact Q'.eqv_trans _ _ _ hinputMeanStage
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (centralPhysicalSmulGNS_B_eq
            w hw stage half raw centralPhysicalLinearVacuum.value))
        (centralPhysicalWeightedInner_vacuum_right
          w hw stage half raw))
  have hactionMeanInput :=
    innerLimit_markovCutoffAction_vacuum_approx_eqv
      hw0 hw1 half stage (X.seq stage)
  have hstationary : mean ≈
      centralPhysicalStationaryMean w hw stage half raw :=
    centralPhysicalStationaryMean_markovApply w hw stage half raw
  have hmean :
      (innerLimit hw0 hw1 half
        ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
        centralPhysicalLinearVacuum).approx stage ≈ mean := by
    exact Q'.eqv_trans _ _ _ hactionMeanInput
      (Q'.eqv_trans _ _ _ hinputMean (Q'.eqv_symm hstationary))
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro k
  change D.B
      (centralPhysicalMarkovApply w hw stage half centered)
      (centralPhysicalMarkovApply w hw stage half centered) ≈
    (innerLimit hw0 hw1 half
        ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
        ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)).approx stage +
      -((innerLimit hw0 hw1 half
          ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
          centralPhysicalLinearVacuum).approx stage *
        (innerLimit hw0 hw1 half
          ((centralPhysicalLinearMarkovMapCauchy M X).seq stage)
          centralPhysicalLinearVacuum).approx stage)
  exact Q'.eqv_trans _ _ _ hwelldef
    (Q'.eqv_trans _ _ _ hcentered
      (Q'.add_eqv_congr'
        (Q'.eqv_symm hraw)
        (Q'.neg_eqv_congr _ _
          (qmul_eqv_congr (Q'.eqv_symm hmean) (Q'.eqv_symm hmean)))))

/-! ## 5. Contracting the four diagonal limits to the two graph norms -/

theorem inputCenteredNorm_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageNorm hw0 hw1 half X)
      (physicalCauchyPairingLimit hw0 hw1 half X X) := by
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (X.seq stage) (X.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (X.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half X X) := by
    simpa only [rawSeq] using cofinality.inputSquare_converges X
  have hmeanRaw := cofinality.inputMean_converges X
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq] using hmeanRaw)
    exact completed_orthogonal_pairing_equiv_zero X horthogonal
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
      (physicalCauchyPairingLimit hw0 hw1 half X X) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half X X))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageNorm_equiv_diagonal hw0 hw1 half X stage)
  · simpa only [rawSeq, meanSeq] using hcenteredLimit

theorem transferredCenteredNorm_converges
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalCutoffCenteredStageTransferredNorm
        hw0 hw1 half X)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalLinearMarkovMapCauchy M X)
        (centralPhysicalLinearMarkovMapCauchy M X)) := by
  let TX := centralPhysicalLinearMarkovMapCauchy M X
  let rawSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TX.seq stage) (TX.seq stage)).approx stage)
  let meanSeq := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (TX.seq stage) centralPhysicalLinearVacuum).approx stage)
  have hraw : CReal.ConvergesTo rawSeq
      (physicalCauchyPairingLimit hw0 hw1 half TX TX) := by
    simpa only [rawSeq, TX] using cofinality.actionSquare_converges M X
  have hmeanRaw := cofinality.actionMean_converges M X
  have hactionInput : CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TX
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
    simpa only [TX] using
      (physicalCauchyPairingLimit_markov_vacuum_equiv
        M cofinality.vacuum.toDiagonalControl X)
  have hmeanTarget : CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half TX
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero :=
    CReal.Equiv.trans hactionInput
      (completed_orthogonal_pairing_equiv_zero X horthogonal)
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr
      (by simpa only [meanSeq, TX] using hmeanRaw)
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
      (physicalCauchyPairingLimit hw0 hw1 half TX TX) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (physicalCauchyPairingLimit hw0 hw1 half TX TX))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (centeredStageTransferredNorm_equiv_diagonal
        hw0 hw1 half M X stage)
  · simpa only [rawSeq, meanSeq, TX] using hcenteredLimit

/-- The explicit four-rate cofinality datum inhabits exactly the two-field
centered graph-norm convergence residual isolated by the prior compiler. -/
def toCenteredGraphNormConvergence
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence
      hw0 hw1 half M where
  norm_converges := cofinality.inputCenteredNorm_converges
  transferredNorm_converges := cofinality.transferredCenteredNorm_converges M

/-- One completion modulus, the explicit four diagonal cofinality rates, and
the finite fixed-nome sixteenth now contract all the way to strictness of the
actual cutoff-removed transfer on its actual completed vacuum complement. -/
def toStrictContractionData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (cofinality : CentralPhysicalLinearMarkovGraphNormInnerCofinality
      hw0 hw1 half)
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (certificate : FixedNomeCutoffCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalCutoffCompletedMarkovStrictContractionData
      hw0 hw1 half M cofinality.vacuum.toPairingInvariant :=
  (cofinality.toCenteredGraphNormConvergence M).toStrictContractionData
    certificate

end CentralPhysicalLinearMarkovGraphNormInnerCofinality

/-! ## Axiom audit -/

#print axioms physicalCauchyPairingDiagonal_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.inputSquare_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.inputMean_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.actionSquare_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.actionMean_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.centeredStageNorm_equiv_diagonal
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.centeredStageTransferredNorm_equiv_diagonal
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.inputCenteredNorm_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.transferredCenteredNorm_converges
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.toCenteredGraphNormConvergence
#print axioms CentralPhysicalLinearMarkovGraphNormInnerCofinality.toStrictContractionData

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality
