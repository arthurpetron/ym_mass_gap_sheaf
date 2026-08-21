/-
# The physical BF4 centered finite gap passes to the completed vacuum complement

The finite physical BF4 producer proves its uniform `1/16` quadratic bound
for every observable whose stationary row-marginal mean is zero.  A general
Cauchy representative of a completed vacuum-orthogonal vector need not have
mean-zero stages.  This module subtracts each stage's exact rational mean,
proves the centered norm and Markov-form identities, and passes the finite
bound through the explicit constructive-real completion.

This is a finite-cutoff completed physical gap.  It does not construct a
thermodynamic or continuum limit and makes no Clay claim.
-/

import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
import YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
import YMGap.Continuum.BF4PhysicalSeparatorProducer

namespace YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact stationary centering at one finite physical stage -/

/-- Subtracting a constant subtracts it from the normalized physical mean. -/
theorem centralPhysicalStationaryMean_add_neg_constant
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') (constant : Q') :
    centralPhysicalStationaryMean w hw K half
        (fun state => observable state + (-constant)) ≈
      centralPhysicalStationaryMean w hw K half observable + (-constant) := by
  let states := centralPositiveHalfStates w hw K half
  let marginal := centralPhysicalRowMarginal w hw K half
  unfold centralPhysicalStationaryMean
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        marginal state * observable state + (-constant) * marginal state)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact Q'.eqv_trans _
      (marginal state * observable state + marginal state * (-constant)) _
      (Q'.mul_add_eqv (marginal state) (observable state) (-constant))
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (marginal state) (-constant)))
  refine Q'.eqv_trans _
    (listQSum (fun state => marginal state * observable state) states +
      listQSum (fun state => (-constant) * marginal state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum (fun state => marginal state * observable state) states +
      (-constant) * listQSum marginal states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left (-constant) marginal states)) ?_
  refine Q'.eqv_trans _
    (listQSum (fun state => marginal state * observable state) states +
      (-constant) * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left (-constant) _ _
        (centralPositiveRowMarginal_total_one w hw K half))
  exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_one_eqv (-constant))

/-- Exact rational centering by the actual stationary row marginal. -/
def centralPhysicalCenteredObservable
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') (state : EdgeLabelling) : Q' :=
  observable state +
    -centralPhysicalStationaryMean w hw K half observable

/-- Every exactly centered finite physical observable has stationary mean zero. -/
theorem centralPhysicalCenteredObservable_meanZero
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    CentralPhysicalMeanZero w hw K half
      (centralPhysicalCenteredObservable w hw K half observable) := by
  unfold CentralPhysicalMeanZero centralPhysicalCenteredObservable
  let mean := centralPhysicalStationaryMean w hw K half observable
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean w hw K half observable + (-mean)) _ ?_ ?_
  · exact centralPhysicalStationaryMean_add_neg_constant
      w hw K half observable mean
  exact Q'.add_neg_self_eqv mean

/-- The pointwise centered observable is the GNS subtraction of its scalar
vacuum component. -/
theorem centralPhysicalCenteredObservable_veq_sub_smul
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    let D := (centralPhysicalSmulGNS w hw K half).toGNSData
    let mean := centralPhysicalStationaryMean w hw K half observable
    D.veq
      (centralPhysicalCenteredObservable w hw K half observable)
      (D.sub observable (D.smul mean centralPhysicalVacuumCarrier)) := by
  dsimp only
  intro state
  unfold centralPhysicalCenteredObservable GNSData.sub centralPhysicalSmulGNS
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_symm
        (Q'.mul_one_eqv
          (centralPhysicalStationaryMean w hw K half observable))))

/-! ## 2. The two centered quadratic identities -/

/-- Pure GNS algebra: subtracting `mean * vacuum`, when the vacuum is unit and
the vacuum pairing is `mean`, subtracts exactly `mean^2` from the diagonal. -/
theorem gns_centered_diag_eqv
    (D : GNSData) (observable vacuum : D.V) (mean : Q')
    (hmean : D.B observable vacuum ≈ mean)
    (hunit : D.B vacuum vacuum ≈ 1) :
    D.B (D.sub observable (D.smul mean vacuum))
        (D.sub observable (D.smul mean vacuum)) ≈
      D.B observable observable + -(mean * mean) := by
  have hcross : D.B observable (D.smul mean vacuum) ≈ mean * mean :=
    Q'.eqv_trans _ _ _ (D.B_smul_right mean observable vacuum)
      (Q'.mul_eqv_congr_left mean _ _ hmean)
  have hscaledSelf :
      D.B (D.smul mean vacuum) (D.smul mean vacuum) ≈ mean * mean := by
    refine Q'.eqv_trans _ (mean * D.B vacuum (D.smul mean vacuum)) _
      (D.B_smul_left mean vacuum (D.smul mean vacuum)) ?_
    refine Q'.eqv_trans _ (mean * (mean * D.B vacuum vacuum)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left mean _ _
        (D.B_smul_right mean vacuum vacuum)
    refine Q'.eqv_trans _ (mean * (mean * 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left mean _ _
        (Q'.mul_eqv_congr_left mean _ _ hunit)
    q_ring
  refine Q'.eqv_trans _
    (((D.B observable observable) +
        (-(D.B observable (D.smul mean vacuum)))) +
      ((-(D.B observable (D.smul mean vacuum))) +
        D.B (D.smul mean vacuum) (D.smul mean vacuum))) _
    (D.B_sub_diag_expand observable (D.smul mean vacuum)) ?_
  refine Q'.eqv_trans _
    (((D.B observable observable) + (-(mean * mean))) +
      ((-(mean * mean)) + (mean * mean))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hcross))
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ hcross) hscaledSelf)
  exact Q'.eqv_trans _
    ((D.B observable observable + -(mean * mean)) + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_add_self_eqv (mean * mean)))
    (Q'.eqv_of_eq (Q'.add_zero' _))

/-- Centering subtracts the squared stationary mean from the physical norm. -/
theorem centralPhysicalCenteredObservable_norm_identity
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    let mean := centralPhysicalStationaryMean w hw K half observable
    centralPhysicalWeightedInner w hw K half
        (centralPhysicalCenteredObservable w hw K half observable)
        (centralPhysicalCenteredObservable w hw K half observable) ≈
      centralPhysicalWeightedInner w hw K half observable observable +
        -(mean * mean) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half observable
  have hcenter := D.B_diag_congr
    (centralPhysicalCenteredObservable_veq_sub_smul
      w hw K half observable)
  have hdiag := gns_centered_diag_eqv D observable
    centralPhysicalVacuumCarrier mean
    (centralPhysicalWeightedInner_vacuum_right w hw K half observable)
    (centralPhysicalWeightedInner_vacuum_one w hw K half)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq w hw K half _ _)) hcenter)
    (Q'.eqv_trans _ _ _ hdiag
      (Q'.add_eqv_congr' (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq w hw K half observable observable))
        (Q'.eqv_refl _)))

/-- Centering subtracts the same squared stationary mean from the positive
physical Markov form `(f,g) |-> <T f,g>`. -/
theorem centralPhysicalCenteredObservable_markovForm_identity
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    let mean := centralPhysicalStationaryMean w hw K half observable
    centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half
          (centralPhysicalCenteredObservable w hw K half observable))
        (centralPhysicalCenteredObservable w hw K half observable) ≈
      centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half observable) observable +
          -(mean * mean) := by
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half observable
  have hcenter : E.veq
      (centralPhysicalCenteredObservable w hw K half observable)
      (E.sub observable (E.smul mean centralPhysicalVacuumCarrier)) :=
    centralPhysicalCenteredObservable_veq_sub_smul
      w hw K half observable
  have hformMean : E.B observable centralPhysicalVacuumCarrier ≈ mean := by
    refine Q'.eqv_trans _
      (centralPhysicalStationaryMean w hw K half
        (centralPhysicalMarkovApply w hw K half observable)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (centralPhysicalMarkovFormGNS_B_eq
          w hw K half observable centralPhysicalVacuumCarrier))
        (centralPhysicalWeightedInner_vacuum_right w hw K half
          (centralPhysicalMarkovApply w hw K half observable))
    exact centralPhysicalStationaryMean_markovApply w hw K half observable
  have hformUnit : E.B centralPhysicalVacuumCarrier
      centralPhysicalVacuumCarrier ≈ 1 := by
    refine Q'.eqv_trans _
      (centralPhysicalStationaryMean w hw K half
        (centralPhysicalMarkovApply w hw K half
          centralPhysicalVacuumCarrier)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (centralPhysicalMarkovFormGNS_B_eq
          w hw K half centralPhysicalVacuumCarrier
            centralPhysicalVacuumCarrier))
        (centralPhysicalWeightedInner_vacuum_right w hw K half
          (centralPhysicalMarkovApply w hw K half
            centralPhysicalVacuumCarrier))
    exact Q'.eqv_trans _ _ _
      (centralPhysicalStationaryMean_markovApply w hw K half
        centralPhysicalVacuumCarrier)
      (centralPhysicalStationaryMean_one w hw K half)
  have hdiag := gns_centered_diag_eqv E observable
    centralPhysicalVacuumCarrier mean hformMean hformUnit
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalMarkovFormGNS_B_eq w hw K half _ _))
      (E.B_diag_congr hcenter))
    (Q'.eqv_trans _ _ _ hdiag
      (Q'.add_eqv_congr'
        (Q'.eqv_of_eq (centralPhysicalMarkovFormGNS_B_eq
          w hw K half observable observable))
        (Q'.eqv_refl _)))

/-! ## 3. Centered sequences of an explicit completion representative -/

private theorem creal_ofQ'_centered_equiv (raw mean : Q') :
    CReal.Equiv
      (CReal.ofQ' (raw + -(mean * mean)))
      (CReal.add (CReal.ofQ' raw)
        (CReal.neg
          (CReal.mul (CReal.ofQ' mean) (CReal.ofQ' mean)))) :=
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

/-- The exact stationary mean of every stage of one physical GNS Cauchy
representative, embedded as a constructive real. -/
def centralPhysicalCauchyMeanSeq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (stage : Nat) : CReal :=
  CReal.ofQ'
    (centralPhysicalStationaryMean w hw K half (X.seq stage))

/-- The stagewise centered physical norm, written using its exact
`raw norm - mean^2` identity. -/
def centralPhysicalCauchyCenteredNormSeq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (stage : Nat) : CReal :=
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half (X.seq stage)
  CReal.ofQ' (D.B (X.seq stage) (X.seq stage) + -(mean * mean))

/-- The stagewise centered physical Markov form, written using its exact
`raw form - mean^2` identity. -/
def centralPhysicalCauchyCenteredMarkovFormSeq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (stage : Nat) : CReal :=
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half (X.seq stage)
  CReal.ofQ' (E.B (X.seq stage) (X.seq stage) + -(mean * mean))

/-- Vacuum orthogonality of the completed class makes the rational stationary
mean of every chosen representative converge to zero. -/
theorem centralPhysicalCauchyMeanSeq_converges_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS w hw K half).toGNSData) X)) :
    CReal.ConvergesTo
      (centralPhysicalCauchyMeanSeq w hw K half X) CReal.czero := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let vacuumRep := constCauchy D centralPhysicalVacuumCarrier
  have hpair : CReal.ConvergesTo
      (fun stage => CReal.ofQ' (D.cInnerSeq X vacuumRep stage))
      (D.cinnerRep X vacuumRep) :=
    CReal.convergesTo_ofQ'CauchySeq
      (D.cInnerSeq X vacuumRep) (D.cInnerQCauchy X vacuumRep)
  have hmean : CReal.ConvergesTo
      (centralPhysicalCauchyMeanSeq w hw K half X)
      (D.cinnerRep X vacuumRep) := by
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s := fun stage => CReal.ofQ' (D.cInnerSeq X vacuumRep stage))
    · intro stage
      exact CReal.ofQ'_equiv_of_eqv
        (centralPhysicalWeightedInner_vacuum_right
          w hw K half (X.seq stage))
    · simpa only [D, vacuumRep, GNSData.cInnerSeq,
        constCauchy, centralPhysicalSmulGNS_B_eq] using hpair
  have hquotient :
      Quotient.mk CReal.crealSetoid (D.cinnerRep X vacuumRep) =
        Quotient.mk CReal.crealSetoid CReal.czero := by
    exact horthogonal
  exact CReal.convergesTo_limit_congr hmean (Quotient.exact hquotient)

/-- The stagewise centered physical norms converge to the ordinary completed
self-pairing when the completed vector is vacuum orthogonal. -/
theorem centralPhysicalCauchyCenteredNormSeq_converges_self
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS w hw K half).toGNSData) X)) :
    CReal.ConvergesTo
      (centralPhysicalCauchyCenteredNormSeq w hw K half X)
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep X X) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let meanSeq := centralPhysicalCauchyMeanSeq w hw K half X
  let rawSeq := fun stage => CReal.ofQ' (D.cInnerSeq X X stage)
  have hraw : CReal.ConvergesTo rawSeq (D.cinnerRep X X) :=
    CReal.convergesTo_ofQ'CauchySeq (D.cInnerSeq X X) (D.cInnerQCauchy X X)
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using
      (centralPhysicalCauchyMeanSeq_converges_zero
        w hw K half X horthogonal)
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
      (D.cinnerRep X X) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (D.cinnerRep X X))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (creal_ofQ'_centered_equiv
        (D.B (X.seq stage) (X.seq stage))
        (centralPhysicalStationaryMean w hw K half (X.seq stage)))
  · simpa only [centralPhysicalCauchyCenteredNormSeq, rawSeq, meanSeq,
      D, GNSData.cInnerSeq] using hcenteredLimit

/-- The stagewise centered physical Markov forms converge to the completed
matrix coefficient `<T X,X>` on a vacuum-orthogonal completed vector. -/
theorem centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS w hw K half).toGNSData) X)) :
    CReal.ConvergesTo
      (centralPhysicalCauchyCenteredMarkovFormSeq w hw K half X)
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X) X) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let TX := (centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X
  let meanSeq := centralPhysicalCauchyMeanSeq w hw K half X
  let rawSeq := fun stage => CReal.ofQ' (D.cInnerSeq TX X stage)
  have hraw : CReal.ConvergesTo rawSeq (D.cinnerRep TX X) :=
    CReal.convergesTo_ofQ'CauchySeq
      (D.cInnerSeq TX X) (D.cInnerQCauchy TX X)
  have hmean : CReal.ConvergesTo meanSeq CReal.czero := by
    simpa only [meanSeq] using
      (centralPhysicalCauchyMeanSeq_converges_zero
        w hw K half X horthogonal)
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
      (D.cinnerRep TX X) := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact CReal.Equiv.trans (CReal.add_congr_right creal_neg_czero)
      (creal_add_czero (D.cinnerRep TX X))
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => CReal.add (rawSeq stage)
      (CReal.neg (CReal.mul (meanSeq stage) (meanSeq stage))))
  · intro stage
    exact CReal.Equiv.symm
      (creal_ofQ'_centered_equiv
        (E.B (X.seq stage) (X.seq stage))
        (centralPhysicalStationaryMean w hw K half (X.seq stage)))
  · simpa only [centralPhysicalCauchyCenteredMarkovFormSeq,
      rawSeq, meanSeq, D, E, TX, GNSData.cInnerSeq,
      DiagonalTransferSymbol.cDiagCauchy,
      centralPhysicalMarkovSymbol_Dv_eq,
      centralPhysicalMarkovFormGNS_B_eq] using hcenteredLimit

/-! ## 4. The finite producer bound on the corrected arbitrary-stage form -/

/-- Any absolute finite mean-zero BF4 form bound becomes a corrected form
bound for an arbitrary observable after exact stationary centering. -/
theorem centralPhysical_centeredCorrection_form_le_of_abs_gap
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (rate : Q')
    (hgap : ∀ observable : EdgeLabelling → Q',
      CentralPhysicalMeanZero w hw K half observable →
        Q'.abs (centralPhysicalJointQuadratic w hw K half observable) ≤
          rate * centralPhysicalWeightedInner w hw K half
            observable observable)
    (observable : EdgeLabelling → Q') :
    let D := (centralPhysicalSmulGNS w hw K half).toGNSData
    let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
    let mean := centralPhysicalStationaryMean w hw K half observable
    E.B observable observable + -(mean * mean) ≤
      rate * (D.B observable observable + -(mean * mean)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half observable
  let centered := centralPhysicalCenteredObservable w hw K half observable
  have hmeanZero : CentralPhysicalMeanZero w hw K half centered :=
    centralPhysicalCenteredObservable_meanZero w hw K half observable
  have hEJoint : E.B centered centered ≈
      centralPhysicalJointQuadratic w hw K half centered := by
    refine Q'.eqv_trans _
      (centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half centered) centered) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (centralPhysicalMarkovFormGNS_B_eq
          w hw K half centered centered)
    refine Q'.eqv_trans _
      (centralPhysicalWeightedInner w hw K half centered
        (centralPhysicalMarkovApply w hw K half centered)) _ ?_ ?_
    · exact Q'.eqv_symm
        (centralPhysicalMarkovApply_self_adjoint
          w hw K half centered centered)
    exact centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw K half centered
  have hcenteredFinite : E.B centered centered ≤ rate * D.B centered centered := by
    refine Q'.le_trans' _
      (centralPhysicalJointQuadratic w hw K half centered) _
      (Q'.le_of_eqv hEJoint) ?_
    refine Q'.le_trans' _
      (Q'.abs (centralPhysicalJointQuadratic w hw K half centered)) _
      (Q'.le_abs_self _) ?_
    refine le_of_le_eqv (hgap centered hmeanZero) ?_
    exact Q'.mul_eqv_congr_left rate _ _
      (Q'.eqv_symm
        (Q'.eqv_of_eq
          (centralPhysicalSmulGNS_B_eq w hw K half centered centered)))
  have hleft : E.B centered centered ≈
      E.B observable observable + -(mean * mean) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalMarkovFormGNS_B_eq w hw K half centered centered))
      (centralPhysicalCenteredObservable_markovForm_identity
        w hw K half observable)
  have hright : D.B centered centered ≈
      D.B observable observable + -(mean * mean) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq w hw K half centered centered))
      (centralPhysicalCenteredObservable_norm_identity
        w hw K half observable)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv hcenteredFinite
      (Q'.mul_eqv_congr_left rate _ _ hright))

/-- At every matched scale, the physical producer's kernel-checked `1/16`
mean-zero estimate controls the corrected arbitrary-stage Markov form. -/
theorem producer_centeredCorrection_form_le_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) (observable : EdgeLabelling → Q') :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let E := (centralPhysicalMarkovFormGNS w hw K 0).toGNSData
    let mean := centralPhysicalStationaryMean w hw K 0 observable
    E.B observable observable + -(mean * mean) ≤
      Q'.mkPos 1 16 (by decide) *
        (D.B observable observable + -(mean * mean)) := by
  exact centralPhysical_centeredCorrection_form_le_of_abs_gap
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (Q'.mkPos 1 16 (by decide))
    (fun centered hcentered =>
      producer.physical_joint_quadratic_abs_le_sixteenth_at
        scale centered hcentered)
    observable

/-! ## 5. Passage of the physical `1/16` form gap to the completion -/

/-- Termwise corrected form bound for one representative at a matched scale. -/
theorem producer_cauchyCenteredFormSeq_le_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 X stage)
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 16 (by decide)))
        (centralPhysicalCauchyCenteredNormSeq
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 X stage)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K 0).toGNSData
  let mean := centralPhysicalStationaryMean w hw K 0 (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection ≤
      Q'.mkPos 1 16 (by decide) * normCorrection := by
    exact producer_centeredCorrection_form_le_sixteenth
      producer scale (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  have hmul := CRealAlg.ofQ'_mul
    (Q'.mkPos 1 16 (by decide)) normCorrection
  exact CReal.leEv_of_equiv hmul

/-- Representative-level completed physical form gap at a matched scale. -/
theorem producer_cinnerRep_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData) X)) :
    CReal.leEv
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 16 (by decide)))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
            X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 X horthogonal)
    (CReal.convergesTo_constMul (Q'.mkPos 1 16 (by decide))
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 X horthogonal))
  exact producer_cauchyCenteredFormSeq_le_sixteenth producer scale X

/-- The actual completed physical BF4 macro transfer has the strict `1/16`
form gap on its entire completed vacuum complement at every matched scale. -/
theorem producer_completed_vacuum_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector) vector)
      (CReal.RCscale (Q'.mkPos 1 16 (by decide))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
            vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact producer_cinnerRep_form_gap_sixteenth
    producer scale X horthogonal

end YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap

#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCenteredObservable_meanZero
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCenteredObservable_norm_identity
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCenteredObservable_markovForm_identity
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCauchyMeanSeq_converges_zero
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCauchyCenteredNormSeq_converges_self
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.producer_centeredCorrection_form_le_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.producer_cinnerRep_form_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap.producer_completed_vacuum_form_gap_sixteenth
