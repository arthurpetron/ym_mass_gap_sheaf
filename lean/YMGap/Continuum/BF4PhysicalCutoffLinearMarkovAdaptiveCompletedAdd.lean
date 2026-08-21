/-
# Zero and addition laws for the adaptive completed BF4 transfer

The adaptive completed transfer is defined by representative-dependent slow
samplers, so its linearity is not a pointwise definitional fact.  This file
proves the first two laws.

Zero follows from dense agreement.  For addition, compare the independently
sampled output of the sum representative and the sum of the two independently
sampled outputs with one common fixed raw anchor.  The sum side costs one
sixteenth; the two component sides cost four sixteenths through the existing
quadratic-Lipschitz addition law; the final triangle costs ten sixteenths.

## Axiom gate

Only explicit adaptive rates, finite-linear addition, the proved
quadratic-Lipschitz bound, and quotient soundness are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Zero -/

theorem centralPhysicalAdaptiveCompletedMarkovTransfer_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (completedPhysicalLinearZero hw0 hw1 half) =
      completedPhysicalLinearZero hw0 hw1 half := by
  exact Eq.trans
    (centralPhysicalAdaptiveCompletedMarkovTransfer_embed pointwise zero)
    (centralPhysicalLinearMarkovDenseTransfer_zero pointwise)

/-! ## 2. Pair-adaptive addition comparison -/

private def adaptiveAddAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let Z := (physicalLinearAddQuadraticLipschitz
    hw0 hw1 half).mapCauchy X Y
  max (Z.modulus slack)
    (max (X.modulus slack) (Y.modulus slack))

private def adaptiveAddThreshold
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let pairTolerance := HalfPow.half * slack
  max (adaptiveAddAnchor X Y epsilon)
    (max (CReal.lv tiny) (CReal.lv pairTolerance))

def centralPhysicalAdaptiveMarkovAddCloseRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let Z := (physicalLinearAddQuadraticLipschitz
    hw0 hw1 half).mapCauchy X Y
  let threshold := adaptiveAddThreshold X Y epsilon
  max
    (centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise Z threshold)
    (max
      (centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise X threshold)
      (centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise Y threshold))

def centralPhysicalAdaptiveMarkovMapAddClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    let Z := (physicalLinearAddQuadraticLipschitz
      hw0 hw1 half).mapCauchy X Y
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise Z)
      ((physicalLinearAddQuadraticLipschitz
        hw0 hw1 half).mapCauchy
          (centralPhysicalAdaptiveMarkovMapCauchy pointwise X)
          (centralPhysicalAdaptiveMarkovMapCauchy pointwise Y)) := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Z := (physicalLinearAddQuadraticLipschitz
    hw0 hw1 half).mapCauchy X Y
  refine
    { modulus := centralPhysicalAdaptiveMarkovAddCloseRate pointwise X Y
      close := ?_ }
  intro epsilon hepsilon stage hstage
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let pairTolerance := HalfPow.half * slack
  let anchor := adaptiveAddAnchor X Y epsilon
  let threshold := adaptiveAddThreshold X Y epsilon
  let zIndex := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise Z stage
  let xIndex := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise X stage
  let yIndex := centralPhysicalAdaptiveMarkovSampleIndex
    hw0 hw1 half pointwise Y stage
  have htiny : (0 : Q') < tiny := adaptiveSixteenth_pos hepsilon
  have hslack : (0 : Q') < slack :=
    ExpNeg.half_mul_pos tiny htiny
  have hpairTolerance : (0 : Q') < pairTolerance :=
    ExpNeg.half_mul_pos slack hslack
  have hZstage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise Z threshold <= stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hXstage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X threshold <= stage :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      hstage
  have hYstage : centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise Y threshold <= stage :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      hstage
  have hZpaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise Z anchor tiny pairTolerance
    htiny hpairTolerance stage hZstage
  have hXpaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise X anchor tiny pairTolerance
    htiny hpairTolerance stage hXstage
  have hYpaid := centralPhysicalAdaptiveMarkov_requirements_paid
    hw0 hw1 half pointwise Y anchor tiny pairTolerance
    htiny hpairTolerance stage hYstage
  have hZmod : Z.modulus slack <= anchor := Nat.le_max_left _ _
  have hXmod : X.modulus slack <= anchor :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hYmod : Y.modulus slack <= anchor :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_refl _)
  have hZinput : CReal.leEv
      (D.distSq (Z.seq zIndex) (Z.seq anchor))
      (CReal.ofQ' slack) :=
    Z.isCauchy slack hslack zIndex anchor
      (Nat.le_trans hZmod hZpaid.1) hZmod
  have hXinput : CReal.leEv
      (D.distSq (X.seq xIndex) (X.seq anchor))
      (CReal.ofQ' slack) :=
    X.isCauchy slack hslack xIndex anchor
      (Nat.le_trans hXmod hXpaid.1) hXmod
  have hYinput : CReal.leEv
      (D.distSq (Y.seq yIndex) (Y.seq anchor))
      (CReal.ofQ' slack) :=
    Y.isCauchy slack hslack yIndex anchor
      (Nat.le_trans hYmod hYpaid.1) hYmod
  have hleft := sameCutoffAnchorDistance_le
    hw0 hw1 half stage (Z.seq zIndex) (Z.seq anchor)
    tiny htiny hZinput hZpaid.2.2
  have hX := sameCutoffAnchorDistance_le
    hw0 hw1 half stage (X.seq xIndex) (X.seq anchor)
    tiny htiny hXinput hXpaid.2.2
  have hY := sameCutoffAnchorDistance_le
    hw0 hw1 half stage (Y.seq yIndex) (Y.seq anchor)
    tiny htiny hYinput hYpaid.2.2
  let leftPoint := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) stage half (Z.seq zIndex)
  let common := centralPhysicalLinearMarkovCutoffAction
    (Q'.le_of_lt hw0) stage half (Z.seq anchor)
  let rightPoint := add
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq xIndex))
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (Y.seq yIndex))
  have hrightRaw := physicalLinearDistSq_add_le hw0 hw1 half
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq xIndex))
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq anchor))
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (Y.seq yIndex))
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (Y.seq anchor))
  have hright : CReal.leEv (D.distSq rightPoint common)
      (CReal.add
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))) :=
    CReal.leEv_trans hrightRaw
      (CReal.leEv_add
        (CReal.leEv_add hX hX)
        (CReal.leEv_add hY hY))
  have hrightSymm : CReal.leEv (D.distSq common rightPoint)
      (CReal.add
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv (D.distSq_symm common rightPoint)) hright
  have htotal := CReal.leEv_trans
    (D.distSq_triangle leftPoint common rightPoint)
    (CReal.leEv_add
      (CReal.leEv_add hleft hleft)
      (CReal.leEv_add hrightSymm hrightSymm))
  have hconstant : CReal.leEv
      (CReal.add
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
        (CReal.add
          (CReal.add
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)))
          (CReal.add
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)))))
      (CReal.ofQ' epsilon) := by
    simp only [CReal.ofQ'_add]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ' (ten_sixteenths_le epsilon hepsilon))
  exact CReal.leEv_trans htotal hconstant

/-! ## 3. Completed addition law -/

theorem centralPhysicalAdaptiveCompletedMarkovTransfer_add
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (completedPhysicalLinearAdd hw0 hw1 half left right) =
      completedPhysicalLinearAdd hw0 hw1 half
        (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise left)
        (centralPhysicalAdaptiveCompletedMarkovTransfer pointwise right) := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨centralPhysicalAdaptiveMarkovMapAddClose pointwise X Y⟩

#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_zero
#print axioms centralPhysicalAdaptiveMarkovMapAddClose
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_add

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd
