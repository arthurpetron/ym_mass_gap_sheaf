/-
# Rational linearity of the adaptive completed BF4 transfer

The adaptive transfer already preserves zero and addition.  Rational scaling
requires one more quotient-level comparison because the scaled representative
and the original representative choose independent slow indices.

At one late action cutoff, compare both selected terms with one common raw
input anchor.  The scaled representative is controlled directly at a quarter
of the requested tolerance.  On the unscaled side, first request the explicit
`scaleTolerance (scalar * scalar)` needed by the continuous scalar action and
then transport that estimate through scaling.  One squared-distance triangle
uses four quarter tolerances exactly.

The resulting three laws bundle the adaptive transfer as a literal rational-
linear endomorphism of the completed physical carrier.  This removes the old
same-index completion modulus from the construction of the completed linear
operator; the pointwise dense cross-cutoff data remain an explicit analytic
input.

## Axiom gate

Only explicit adaptive rates, rational scalar continuity, finite-linear
syntax, and quotient soundness are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Scalar-adaptive comparison schedule -/

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

private def adaptiveScalarAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (scalar epsilon : Q') : Nat :=
  let q := adaptiveQuarter epsilon
  let scaledTolerance := CReal.InnerRegularity.scaleTolerance
    (scalar * scalar) q
  let S := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).mapCauchy X
  max (S.modulus (HalfPow.half * q))
    (X.modulus (HalfPow.half * scaledTolerance))

private def adaptiveScalarLeftThreshold
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (scalar epsilon : Q') : Nat :=
  let q := adaptiveQuarter epsilon
  let pairTolerance := HalfPow.half * (HalfPow.half * q)
  max (adaptiveScalarAnchor X scalar epsilon)
    (max (CReal.lv q) (CReal.lv pairTolerance))

private def adaptiveScalarRightThreshold
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (scalar epsilon : Q') : Nat :=
  let q := adaptiveQuarter epsilon
  let scaledTolerance := CReal.InnerRegularity.scaleTolerance
    (scalar * scalar) q
  let pairTolerance := HalfPow.half *
    (HalfPow.half * scaledTolerance)
  max (adaptiveScalarAnchor X scalar epsilon)
    (max (CReal.lv q) (CReal.lv pairTolerance))

def centralPhysicalAdaptiveMarkovSmulCloseRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (scalar : Q')
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let S := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).mapCauchy X
  max
    (centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise S
      (adaptiveScalarLeftThreshold X scalar epsilon))
    (centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X
      (adaptiveScalarRightThreshold X scalar epsilon))

/-! ## 2. Independently sampled scalar images are close -/

def centralPhysicalAdaptiveMarkovMapSmulClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (scalar : Q')
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let S := (physicalLinearSmulContinuous
      hw0 hw1 half scalar).mapCauchy X
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise S)
      ((physicalLinearSmulContinuous
        hw0 hw1 half scalar).mapCauchy
          (centralPhysicalAdaptiveMarkovMapCauchy pointwise X)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let S := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).mapCauchy X
  refine
    { modulus := centralPhysicalAdaptiveMarkovSmulCloseRate
        pointwise scalar X
      close := ?_ }
  intro epsilon hepsilon stage hstage
  let q := adaptiveQuarter epsilon
  let scaledTolerance := CReal.InnerRegularity.scaleTolerance
    (scalar * scalar) q
  let leftSlack := HalfPow.half * q
  let rightSlack := HalfPow.half * scaledTolerance
  let leftPairTolerance := HalfPow.half * leftSlack
  let rightPairTolerance := HalfPow.half * rightSlack
  let anchor := adaptiveScalarAnchor X scalar epsilon
  let leftThreshold := adaptiveScalarLeftThreshold X scalar epsilon
  let rightThreshold := adaptiveScalarRightThreshold X scalar epsilon
  let leftIndex := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise S stage
  let rightIndex := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X stage
  have hq : (0 : Q') < q := adaptiveQuarter_pos hepsilon
  have hscaledTolerance : (0 : Q') < scaledTolerance :=
    CReal.InnerRegularity.scaleTolerance_pos
      (scalar * scalar) q hq
  have hleftSlack : (0 : Q') < leftSlack :=
    ExpNeg.half_mul_pos q hq
  have hrightSlack : (0 : Q') < rightSlack :=
    ExpNeg.half_mul_pos scaledTolerance hscaledTolerance
  have hleftPairTolerance : (0 : Q') < leftPairTolerance :=
    ExpNeg.half_mul_pos leftSlack hleftSlack
  have hrightPairTolerance : (0 : Q') < rightPairTolerance :=
    ExpNeg.half_mul_pos rightSlack hrightSlack
  have hleftStage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise S leftThreshold <= stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hrightStage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X rightThreshold <= stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  have hleftPaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise S anchor q leftPairTolerance
    hq hleftPairTolerance stage hleftStage
  have hrightPaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise X anchor q rightPairTolerance
    hq hrightPairTolerance stage hrightStage
  have hleftMod : S.modulus leftSlack <= anchor :=
    Nat.le_max_left _ _
  have hrightMod : X.modulus rightSlack <= anchor :=
    Nat.le_max_right _ _
  have hleftInput : CReal.leEv
      (D.distSq (S.seq leftIndex) (S.seq anchor))
      (CReal.ofQ' leftSlack) :=
    S.isCauchy leftSlack hleftSlack leftIndex anchor
      (Nat.le_trans hleftMod hleftPaid.1) hleftMod
  have hrightInput : CReal.leEv
      (D.distSq (X.seq rightIndex) (X.seq anchor))
      (CReal.ofQ' rightSlack) :=
    X.isCauchy rightSlack hrightSlack rightIndex anchor
      (Nat.le_trans hrightMod hrightPaid.1) hrightMod
  have hleft := sameCutoffAnchorDistance_le
    hw0 hw1 half stage (S.seq leftIndex) (S.seq anchor)
    q hq hleftInput hleftPaid.2.2
  have hrightRaw := sameCutoffAnchorDistance_le
    hw0 hw1 half stage (X.seq rightIndex) (X.seq anchor)
    scaledTolerance hscaledTolerance hrightInput hrightPaid.2.2
  have hright := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).contraction q hq
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half (X.seq rightIndex))
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half (X.seq anchor))
      hrightRaw
  let leftPoint := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) stage half (S.seq leftIndex)
  let common := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) stage half (S.seq anchor)
  let rightPoint := smul scalar
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq rightIndex))
  have hrightSymm : CReal.leEv (D.distSq common rightPoint)
      (CReal.ofQ' q) := by
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (D.distSq_symm common rightPoint))
      hright
  have htotal := CReal.leEv_trans
    (D.distSq_triangle leftPoint common rightPoint)
    (CReal.leEv_add
      (CReal.leEv_add hleft hleft)
      (CReal.leEv_add hrightSymm hrightSymm))
  have hconstant : CReal.leEv
      (CReal.add
        (CReal.add (CReal.ofQ' q) (CReal.ofQ' q))
        (CReal.add (CReal.ofQ' q) (CReal.ofQ' q)))
      (CReal.ofQ' epsilon) := by
    simp only [CReal.ofQ'_add]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (four_adaptiveQuarters_le epsilon))
  exact CReal.leEv_trans htotal hconstant

/-! ## 3. Completed scalar law and rational-linear bundle -/

theorem centralPhysicalAdaptiveCompletedMarkovTransfer_smul
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (scalar : Q')
    (observable : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (completedPhysicalLinearSmul
          hw0 hw1 half scalar observable) =
      completedPhysicalLinearSmul hw0 hw1 half scalar
        (centralPhysicalAdaptiveCompletedMarkovTransfer
          pointwise observable) := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨centralPhysicalAdaptiveMarkovMapSmulClose
    pointwise scalar X⟩

/-- The adaptive completed transfer, from pointwise dense cross-cutoff data,
as a rational-linear endomorphism of the concrete completed carrier. -/
def centralPhysicalAdaptiveCompletedMarkovQLinearEndomorphism
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedQModule hw0 hw1 half) where
  toFun := centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
  map_zero := centralPhysicalAdaptiveCompletedMarkovTransfer_zero pointwise
  map_add := centralPhysicalAdaptiveCompletedMarkovTransfer_add pointwise
  map_smul := centralPhysicalAdaptiveCompletedMarkovTransfer_smul pointwise

#print axioms centralPhysicalAdaptiveMarkovMapSmulClose
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_smul
#print axioms centralPhysicalAdaptiveCompletedMarkovQLinearEndomorphism

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear
