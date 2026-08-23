/-
# A joint adaptive schedule for two completed BF4 vectors

Positive-Markov-form Cauchy--Schwarz must compare two arbitrary completion
representatives at one finite action cutoff.  Independently chosen adaptive
samplers do not provide that alignment.  This file factors the existing
one-vector Cauchy proof through an admissible-sampler interface and constructs
one shared slow diagonal for a pair of representatives.

The shared requirement pays both original adaptive transfer schedules and
the two self-pair plus one cross-pair inner rates.  Consequently its two
same-cutoff Markov images are genuine Cauchy representatives while retaining
the aligned finite positive form needed downstream.

No Cauchy--Schwarz limit or strict rate is asserted here.  No thermodynamic or
continuum limit, or Clay conclusion, is asserted.

## Axiom gate

Only finite running maxima, explicit slow diagonals, rational error budgets,
and the supplied pointwise Markov moduli are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Generic admissible samplers -/

/-- Exactly the three simultaneous payments consumed by the adaptive Markov
Cauchy proof, abstracted from the particular slow selector which supplies
them. -/
structure CentralPhysicalLinearMarkovAdmissibleSample
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Type where
  index : Nat -> Nat
  rate : Nat -> Nat
  paid : forall
    (anchor : Nat)
    (pointwiseTolerance pairTolerance : Q'),
    (0 : Q') < pointwiseTolerance ->
    (0 : Q') < pairTolerance ->
    forall stage,
    rate
      (max anchor
        (max (CReal.lv pointwiseTolerance)
          (CReal.lv pairTolerance))) <= stage ->
    let selected := index stage
    anchor <= selected /\
    regularPhysicalLinearMarkovCrossCutoffRate
      pointwise (X.seq anchor) pointwiseTolerance <= stage /\
    (regularizedInnerRegularity
      (physicalLinearDistSqInnerRegularity hw0 hw1 half
        (X.seq selected) (X.seq anchor))).rate pairTolerance <= stage

/-- Input sampling along any admissible selector remains Cauchy. -/
def centralPhysicalAdmissibleMarkovInputCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (sample : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := X.seq (sample.index stage)
  modulus epsilon := sample.rate
    (max (X.modulus epsilon)
      (max (CReal.lv 1) (CReal.lv 1)))
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    have hone : (0 : Q') < 1 := by decide
    have hfirstPaid := sample.paid (X.modulus epsilon) 1 1
      hone hone first hfirst
    have hsecondPaid := sample.paid (X.modulus epsilon) 1 1
      hone hone second hsecond
    exact X.isCauchy epsilon hepsilon _ _ hfirstPaid.1 hsecondPaid.1

/-- Admissible input sampling preserves the completion class. -/
def centralPhysicalAdmissibleMarkovInputClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (sample : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalAdmissibleMarkovInputCauchy sample) where
  modulus epsilon := max (X.modulus epsilon)
    (sample.rate
      (max (X.modulus epsilon)
        (max (CReal.lv 1) (CReal.lv 1))))
  close := by
    intro epsilon hepsilon stage hstage
    have hone : (0 : Q') < 1 := by decide
    have hraw : X.modulus epsilon <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hsample : sample.rate
        (max (X.modulus epsilon)
          (max (CReal.lv 1) (CReal.lv 1))) <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    have hpaid := sample.paid (X.modulus epsilon) 1 1
      hone hone stage hsample
    exact X.isCauchy epsilon hepsilon stage (sample.index stage)
      hraw hpaid.1

theorem centralPhysicalAdmissibleMarkovInput_class_eq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (sample : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalAdmissibleMarkovInputCauchy sample) :=
  Quotient.sound
    ⟨centralPhysicalAdmissibleMarkovInputClose sample⟩

/-- The same adaptive Cauchy proof works for every selector exposing the
three required payments. -/
def centralPhysicalAdmissibleMarkovMapCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (sample : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) stage half (X.seq (sample.index stage))
  modulus epsilon := sample.rate (adaptiveMarkovCauchyThreshold X epsilon)
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    let tiny := adaptiveSixteenth epsilon
    let slack := HalfPow.half * tiny
    let pairTolerance := HalfPow.half * slack
    let anchor := X.modulus slack
    let firstIndex := sample.index first
    let secondIndex := sample.index second
    have htiny : (0 : Q') < tiny := adaptiveSixteenth_pos hepsilon
    have hslack : (0 : Q') < slack :=
      ExpNeg.half_mul_pos tiny htiny
    have hpairTolerance : (0 : Q') < pairTolerance :=
      ExpNeg.half_mul_pos slack hslack
    have hfirstPaid := sample.paid anchor tiny pairTolerance
      htiny hpairTolerance first hfirst
    have hsecondPaid := sample.paid anchor tiny pairTolerance
      htiny hpairTolerance second hsecond
    have hfirstInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq firstIndex) (X.seq anchor))
        (CReal.ofQ' slack) :=
      X.isCauchy slack hslack firstIndex anchor
        hfirstPaid.1 (Nat.le_refl _)
    have hsecondInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq secondIndex) (X.seq anchor))
        (CReal.ofQ' slack) :=
      X.isCauchy slack hslack secondIndex anchor
        hsecondPaid.1 (Nat.le_refl _)
    have hleft := sameCutoffAnchorDistance_le
      hw0 hw1 half first (X.seq firstIndex) (X.seq anchor)
      tiny htiny hfirstInput hfirstPaid.2.2
    have hmiddle :=
      (regularizedPhysicalLinearMarkovCrossCutoffModulus
        pointwise (X.seq anchor)).cauchy
        tiny htiny first second hfirstPaid.2.1 hsecondPaid.2.1
    have hright := sameCutoffAnchorDistance_le
      hw0 hw1 half second (X.seq secondIndex) (X.seq anchor)
      tiny htiny hsecondInput hsecondPaid.2.2
    let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
    let leftPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) first half (X.seq firstIndex)
    let firstAnchor := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) first half (X.seq anchor)
    let secondAnchor := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) second half (X.seq anchor)
    let rightPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) second half (X.seq secondIndex)
    have hrightSymm : CReal.leEv (D.distSq secondAnchor rightPoint)
        (CReal.ofQ' tiny) :=
      CReal.leEv_trans
        (CReal.leEv_of_equiv (D.distSq_symm secondAnchor rightPoint))
        hright
    exact distSq_threeLeg_le_of_sixteenth (D := D)
      leftPoint firstAnchor secondAnchor rightPoint epsilon hepsilon
      (by simpa only [tiny] using hleft)
      (by simpa only [tiny] using hmiddle)
      (by simpa only [tiny] using hrightSymm)

private theorem four_adaptiveQuarters_le (epsilon : Q') :
    let q := adaptiveQuarter epsilon
    (q + q) + (q + q) <= epsilon := by
  let q := adaptiveQuarter epsilon
  have hpair : (q + q).eqv (HalfPow.half * epsilon) :=
    ExpNeg.two_halves (HalfPow.half * epsilon)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hpair hpair)
      (ExpNeg.two_halves epsilon))

/-- Any two admissible samplers for the same input construct close action
representatives.  Thus admissibility, rather than the selector's literal
formula, determines the completed transfer point. -/
def centralPhysicalAdmissibleMarkovMapClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (left right : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalAdmissibleMarkovMapCauchy left)
      (centralPhysicalAdmissibleMarkovMapCauchy right) where
  modulus epsilon :=
    let tiny := adaptiveQuarter epsilon
    let slack := HalfPow.half * tiny
    let pairTolerance := HalfPow.half * slack
    let threshold := max (X.modulus slack)
      (max (CReal.lv tiny) (CReal.lv pairTolerance))
    max (left.rate threshold) (right.rate threshold)
  close := by
    intro epsilon hepsilon stage hstage
    let tiny := adaptiveQuarter epsilon
    let slack := HalfPow.half * tiny
    let pairTolerance := HalfPow.half * slack
    let anchor := X.modulus slack
    let threshold := max anchor
      (max (CReal.lv tiny) (CReal.lv pairTolerance))
    let leftIndex := left.index stage
    let rightIndex := right.index stage
    have htiny : (0 : Q') < tiny := adaptiveQuarter_pos hepsilon
    have hslack : (0 : Q') < slack :=
      ExpNeg.half_mul_pos tiny htiny
    have hpairTolerance : (0 : Q') < pairTolerance :=
      ExpNeg.half_mul_pos slack hslack
    have hleftStage : left.rate threshold <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hrightStage : right.rate threshold <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    have hleftPaid := left.paid anchor tiny pairTolerance
      htiny hpairTolerance stage hleftStage
    have hrightPaid := right.paid anchor tiny pairTolerance
      htiny hpairTolerance stage hrightStage
    have hleftInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq leftIndex) (X.seq anchor))
        (CReal.ofQ' slack) :=
      X.isCauchy slack hslack leftIndex anchor
        hleftPaid.1 (Nat.le_refl _)
    have hrightInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq rightIndex) (X.seq anchor))
        (CReal.ofQ' slack) :=
      X.isCauchy slack hslack rightIndex anchor
        hrightPaid.1 (Nat.le_refl _)
    have hleft := sameCutoffAnchorDistance_le
      hw0 hw1 half stage (X.seq leftIndex) (X.seq anchor)
      tiny htiny hleftInput hleftPaid.2.2
    have hright := sameCutoffAnchorDistance_le
      hw0 hw1 half stage (X.seq rightIndex) (X.seq anchor)
      tiny htiny hrightInput hrightPaid.2.2
    let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
    let leftPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq leftIndex)
    let common := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq anchor)
    let rightPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq rightIndex)
    have hrightSymm : CReal.leEv (D.distSq common rightPoint)
        (CReal.ofQ' tiny) :=
      CReal.leEv_trans
        (CReal.leEv_of_equiv (D.distSq_symm common rightPoint)) hright
    have htriangle := D.distSq_triangle leftPoint common rightPoint
    have hsum : CReal.leEv
        (CReal.add (D.distSq leftPoint common)
          (D.distSq leftPoint common))
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)) :=
      CReal.leEv_add hleft hleft
    have hsumRight : CReal.leEv
        (CReal.add (D.distSq common rightPoint)
          (D.distSq common rightPoint))
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)) :=
      CReal.leEv_add hrightSymm hrightSymm
    have hcombined := CReal.leEv_add hsum hsumRight
    refine CReal.leEv_trans htriangle (CReal.leEv_trans hcombined ?_)
    simp only [CReal.ofQ'_add]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (four_adaptiveQuarters_le epsilon))

/-- The repository's original adaptive selector is one admissible sampler. -/
def centralPhysicalOriginalAdaptiveMarkovSample
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X where
  index := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X
  rate := centralPhysicalAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise X
  paid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise X

/-- Every admissibly sampled action represents the actual adaptive completed
Markov image of its input. -/
theorem centralPhysicalAdmissibleMarkovMap_class_eq_adaptive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (sample : CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X) :
    Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalAdmissibleMarkovMapCauchy sample) =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalAdaptiveMarkovMapCauchy pointwise X) := by
  apply Quotient.sound
  exact ⟨centralPhysicalAdmissibleMarkovMapClose sample
    (centralPhysicalOriginalAdaptiveMarkovSample
      hw0 hw1 half pointwise X)⟩

/-! ## 2. The shared two-vector slow diagonal -/

def centralPhysicalJointAdaptiveMarkovRequirement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (index : Nat) : Nat :=
  let tolerance := Q'.invSucc index
  max
    (centralPhysicalAdaptiveMarkovRequirement hw0 hw1 half pointwise X index)
    (max
      (centralPhysicalAdaptiveMarkovRequirement hw0 hw1 half pointwise Y index)
      (max
        ((regularizedInnerRegularity
          (innerLimitInnerRegularity hw0 hw1 half
            (X.seq index) (X.seq index))).rate tolerance)
        (max
          ((regularizedInnerRegularity
            (innerLimitInnerRegularity hw0 hw1 half
              (Y.seq index) (Y.seq index))).rate tolerance)
          ((regularizedInnerRegularity
            (innerLimitInnerRegularity hw0 hw1 half
              (X.seq index) (Y.seq index))).rate tolerance))))

def centralPhysicalJointAdaptiveMarkovSampleRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold : Nat) : Nat :=
  slowThreshold
    (centralPhysicalJointAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X Y) threshold

def centralPhysicalJointAdaptiveMarkovSampleIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  slowIndex
    (centralPhysicalJointAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X Y) stage

theorem centralPhysicalJointAdaptiveMarkovSampleIndex_cofinal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold stage : Nat)
    (hstage : centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y threshold <= stage) :
    threshold <= centralPhysicalJointAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X Y stage :=
  slowIndex_cofinal
    (centralPhysicalJointAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X Y) threshold stage hstage

private theorem adaptiveRequirement_paid_at
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (anchor : Nat)
    (pointwiseTolerance pairTolerance : Q')
    (hpointwiseTolerance : (0 : Q') < pointwiseTolerance)
    (hpairTolerance : (0 : Q') < pairTolerance)
    (index stage : Nat)
    (hindex : max anchor
      (max (CReal.lv pointwiseTolerance) (CReal.lv pairTolerance)) <= index)
    (hrequirement : centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X index <= stage) :
    anchor <= index /\
    regularPhysicalLinearMarkovCrossCutoffRate
      pointwise (X.seq anchor) pointwiseTolerance <= stage /\
    (regularizedInnerRegularity
      (physicalLinearDistSqInnerRegularity hw0 hw1 half
        (X.seq index) (X.seq anchor))).rate pairTolerance <= stage := by
  have hanchor : anchor <= index :=
    Nat.le_trans (Nat.le_max_left _ _) hindex
  have hpointPrecision : CReal.lv pointwiseTolerance <= index :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hindex
  have hpairPrecision : CReal.lv pairTolerance <= index :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hindex
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
              (X.seq earlier) (Q'.invSucc index)) index := by
    have hbase := CReal.Gmax_ge
      (fun earlier =>
        regularPhysicalLinearMarkovCrossCutoffRate pointwise
          (X.seq earlier) (Q'.invSucc index)) anchor
    exact Nat.le_trans hbase
      (CReal.Gmax_mono _ anchor index hanchor)
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
                  (Q'.invSucc index)) index := by
    have hbase := CReal.Gmax_ge
      (fun earlier =>
        (regularizedInnerRegularity
          (physicalLinearDistSqInnerRegularity hw0 hw1 half
            (X.seq index) (X.seq earlier))).rate
              (Q'.invSucc index)) anchor
    exact Nat.le_trans hbase
      (CReal.Gmax_mono _ anchor index hanchor)
  have hpairPaid :
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          (X.seq index) (X.seq anchor))).rate pairTolerance <= stage :=
    Nat.le_trans hpairAntitone
      (Nat.le_trans hpairGmax
        (Nat.le_trans (Nat.le_max_right _ _) hrequirement))
  exact ⟨hanchor, hpointPaid, hpairPaid⟩

private theorem joint_requirement_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold stage : Nat)
    (hstage : centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y threshold <= stage) :
    let index := centralPhysicalJointAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X Y stage
    threshold <= index /\
    centralPhysicalJointAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X Y index <= stage := by
  let requirement := centralPhysicalJointAdaptiveMarkovRequirement
    hw0 hw1 half pointwise X Y
  let index := centralPhysicalJointAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X Y stage
  have hindex : threshold <= index :=
    centralPhysicalJointAdaptiveMarkovSampleIndex_cofinal
      hw0 hw1 half pointwise X Y threshold stage hstage
  have hzero : centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y 0 <=
      centralPhysicalJointAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise X Y threshold :=
    slowThreshold_mono requirement (Nat.zero_le _)
  exact ⟨hindex,
    required_slowIndex_le requirement stage (Nat.le_trans hzero hstage)⟩

/-- The shared selector is admissible for its left input. -/
def centralPhysicalJointAdaptiveMarkovLeftSample
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise X where
  index := centralPhysicalJointAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X Y
  rate := centralPhysicalJointAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise X Y
  paid := by
    intro anchor pointwiseTolerance pairTolerance
      hpointwiseTolerance hpairTolerance stage hstage
    let threshold := max anchor
      (max (CReal.lv pointwiseTolerance) (CReal.lv pairTolerance))
    let index := centralPhysicalJointAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X Y stage
    have hpaid := joint_requirement_paid
      hw0 hw1 half pointwise X Y threshold stage hstage
    have hXRequirement : centralPhysicalAdaptiveMarkovRequirement
        hw0 hw1 half pointwise X index <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hpaid.2
    exact adaptiveRequirement_paid_at hw0 hw1 half pointwise X
      anchor pointwiseTolerance pairTolerance
      hpointwiseTolerance hpairTolerance index stage
      hpaid.1 hXRequirement

/-- The same shared selector is admissible for its right input. -/
def centralPhysicalJointAdaptiveMarkovRightSample
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CentralPhysicalLinearMarkovAdmissibleSample
      hw0 hw1 half pointwise Y where
  index := centralPhysicalJointAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X Y
  rate := centralPhysicalJointAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise X Y
  paid := by
    intro anchor pointwiseTolerance pairTolerance
      hpointwiseTolerance hpairTolerance stage hstage
    let threshold := max anchor
      (max (CReal.lv pointwiseTolerance) (CReal.lv pairTolerance))
    let index := centralPhysicalJointAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X Y stage
    have hpaid := joint_requirement_paid
      hw0 hw1 half pointwise X Y threshold stage hstage
    have hYRequirement : centralPhysicalAdaptiveMarkovRequirement
        hw0 hw1 half pointwise Y index <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hpaid.2
    exact adaptiveRequirement_paid_at hw0 hw1 half pointwise Y
      anchor pointwiseTolerance pairTolerance
      hpointwiseTolerance hpairTolerance index stage
      hpaid.1 hYRequirement

/-! ## 3. The four aligned Cauchy representatives -/

def centralPhysicalJointAdaptiveLeftInputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  centralPhysicalAdmissibleMarkovInputCauchy
    (centralPhysicalJointAdaptiveMarkovLeftSample
      hw0 hw1 half pointwise X Y)

def centralPhysicalJointAdaptiveRightInputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  centralPhysicalAdmissibleMarkovInputCauchy
    (centralPhysicalJointAdaptiveMarkovRightSample
      hw0 hw1 half pointwise X Y)

def centralPhysicalJointAdaptiveLeftActionCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  centralPhysicalAdmissibleMarkovMapCauchy
    (centralPhysicalJointAdaptiveMarkovLeftSample
      hw0 hw1 half pointwise X Y)

def centralPhysicalJointAdaptiveRightActionCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  centralPhysicalAdmissibleMarkovMapCauchy
    (centralPhysicalJointAdaptiveMarkovRightSample
      hw0 hw1 half pointwise X Y)

/-! ## 4. The shared selector pays the three Markov-form inner rates -/

/-- At every sufficiently late joint stage, both self rates and the cross
rate of the two selected inputs are paid by the common action cutoff. -/
theorem centralPhysicalJointAdaptiveMarkov_inner_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalJointAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X Y (CReal.lv epsilon) <= stage) :
    let index := centralPhysicalJointAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X Y stage
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) (X.seq index))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (Y.seq index) (Y.seq index))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) (Y.seq index))).rate epsilon <= stage := by
  let index := centralPhysicalJointAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X Y stage
  have hpaid := joint_requirement_paid hw0 hw1 half pointwise X Y
    (CReal.lv epsilon) stage hstage
  have hinv : Q'.invSucc index <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hpaid.1)
      (CReal.invSucc_lv_le hepsilon)
  have hselfXAntitone := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq index) (X.seq index)) (Q'.invSucc_pos index) hinv
  have hselfYAntitone := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      (Y.seq index) (Y.seq index)) (Q'.invSucc_pos index) hinv
  have hcrossAntitone := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq index) (Y.seq index)) (Q'.invSucc_pos index) hinv
  have hselfXBase :
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          (X.seq index) (X.seq index))).rate (Q'.invSucc index) <=
        centralPhysicalJointAdaptiveMarkovRequirement
          hw0 hw1 half pointwise X Y index :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right _ _))
  have hselfYBase :
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          (Y.seq index) (Y.seq index))).rate (Q'.invSucc index) <=
        centralPhysicalJointAdaptiveMarkovRequirement
          hw0 hw1 half pointwise X Y index :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_max_right _ _)))
  have hcrossBase :
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          (X.seq index) (Y.seq index))).rate (Q'.invSucc index) <=
        centralPhysicalJointAdaptiveMarkovRequirement
          hw0 hw1 half pointwise X Y index :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_max_right _ _)))
  exact
    ⟨Nat.le_trans hselfXAntitone (Nat.le_trans hselfXBase hpaid.2),
      Nat.le_trans hselfYAntitone (Nat.le_trans hselfYBase hpaid.2),
      Nat.le_trans hcrossAntitone (Nat.le_trans hcrossBase hpaid.2)⟩

#print axioms centralPhysicalAdmissibleMarkovInputCauchy
#print axioms centralPhysicalAdmissibleMarkovMapCauchy
#print axioms centralPhysicalAdmissibleMarkovMapClose
#print axioms centralPhysicalAdmissibleMarkovMap_class_eq_adaptive
#print axioms centralPhysicalJointAdaptiveMarkovSampleIndex_cofinal
#print axioms centralPhysicalJointAdaptiveMarkovLeftSample
#print axioms centralPhysicalJointAdaptiveMarkovRightSample
#print axioms centralPhysicalJointAdaptiveLeftActionCauchy
#print axioms centralPhysicalJointAdaptiveRightActionCauchy
#print axioms centralPhysicalJointAdaptiveMarkov_inner_rates_paid

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
