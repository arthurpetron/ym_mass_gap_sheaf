/-
# Adaptive completed BF4 Markov transfer from pointwise Cauchy data

The adaptive two-index output is already Cauchy for every input
representative.  This file proves the remaining quotient law: explicitly close
input representatives produce explicitly close adaptive output diagonals,
even though their slow samplers are chosen independently.

At one late action cutoff, choose a common fixed raw input anchor.  Each input
representative is Cauchy-close to its own selected term, the supplied input
closeness controls the two anchor values, and same-cutoff limiting
nonexpansiveness transports all three legs through the Markov action.  The
same ten-sixteenths triangle budget closes the estimate.

Consequently any family of pointwise dense cross-cutoff moduli constructs an
actual endomap of the whole physical cutoff completion.  It agrees with the
previous dense cutoff limit and fixes the normalized completed vacuum.  The
old same-index `CentralPhysicalLinearMarkovCompletionModulus` is not needed for
existence or quotient descent of this adaptive transfer.

## Axiom gate

Only explicit Cauchy/closeness moduli, adaptive finite searches, eventual
orders, and quotient soundness are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Pair-dependent close schedule -/

def centralPhysicalAdaptiveMarkovCloseAnchor
    {D : SquaredSeminorm} {X Y : D.Cauchy}
    (h : D.Close X Y) (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  max (max (X.modulus slack) (Y.modulus slack)) (h.modulus slack)

def centralPhysicalAdaptiveMarkovCloseThreshold
    {D : SquaredSeminorm} {X Y : D.Cauchy}
    (h : D.Close X Y) (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let pairTolerance := HalfPow.half * slack
  max (centralPhysicalAdaptiveMarkovCloseAnchor h epsilon)
    (max (CReal.lv tiny) (CReal.lv pairTolerance))

def centralPhysicalAdaptiveMarkovCloseRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X Y)
    (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let pairTolerance := HalfPow.half * slack
  let anchor := centralPhysicalAdaptiveMarkovCloseAnchor h epsilon
  let threshold := centralPhysicalAdaptiveMarkovCloseThreshold h epsilon
  max
    (centralPhysicalAdaptiveMarkovSampleRate
      hw0 hw1 half pointwise X threshold)
    (max
      (centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise Y threshold)
      ((regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          (X.seq anchor) (Y.seq anchor))).rate pairTolerance))

/-! ## 2. Close input representatives have close adaptive images -/

def centralPhysicalAdaptiveMarkovMapClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X Y) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise X)
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise Y) where
  modulus := centralPhysicalAdaptiveMarkovCloseRate pointwise h
  close := by
    intro epsilon hepsilon stage hstage
    let tiny := adaptiveSixteenth epsilon
    let slack := HalfPow.half * tiny
    let pairTolerance := HalfPow.half * slack
    let anchor := centralPhysicalAdaptiveMarkovCloseAnchor h epsilon
    let threshold := centralPhysicalAdaptiveMarkovCloseThreshold h epsilon
    let leftIndex := centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X stage
    let rightIndex := centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise Y stage
    have htiny : (0 : Q') < tiny := adaptiveSixteenth_pos hepsilon
    have hslack : (0 : Q') < slack :=
      ExpNeg.half_mul_pos tiny htiny
    have hpairTolerance : (0 : Q') < pairTolerance :=
      ExpNeg.half_mul_pos slack hslack
    have hXstage : centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise X threshold <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hYstage : centralPhysicalAdaptiveMarkovSampleRate
        hw0 hw1 half pointwise Y threshold <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        hstage
    have hcentralRate :
        (regularizedInnerRegularity
          (physicalLinearDistSqInnerRegularity hw0 hw1 half
            (X.seq anchor) (Y.seq anchor))).rate pairTolerance <= stage :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        hstage
    have hXpaid := centralPhysicalAdaptiveMarkov_requirements_paid
      hw0 hw1 half pointwise X anchor tiny pairTolerance
      htiny hpairTolerance stage hXstage
    have hYpaid := centralPhysicalAdaptiveMarkov_requirements_paid
      hw0 hw1 half pointwise Y anchor tiny pairTolerance
      htiny hpairTolerance stage hYstage
    have hXmod : X.modulus slack <= anchor :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        (Nat.le_refl _)
    have hYmod : Y.modulus slack <= anchor :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        (Nat.le_refl _)
    have hCloseMod : h.modulus slack <= anchor :=
      Nat.le_max_right _ _
    have hleftInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq leftIndex) (X.seq anchor))
        (CReal.ofQ' slack) :=
      X.isCauchy slack hslack leftIndex anchor
        (Nat.le_trans hXmod hXpaid.1) hXmod
    have hrightInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (Y.seq rightIndex) (Y.seq anchor))
        (CReal.ofQ' slack) :=
      Y.isCauchy slack hslack rightIndex anchor
        (Nat.le_trans hYmod hYpaid.1) hYmod
    have hanchorInput : CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (X.seq anchor) (Y.seq anchor))
        (CReal.ofQ' slack) :=
      h.close slack hslack anchor hCloseMod
    have hleft := sameCutoffAnchorDistance_le
      hw0 hw1 half stage (X.seq leftIndex) (X.seq anchor)
      tiny htiny hleftInput hXpaid.2.2
    have hmiddle := sameCutoffAnchorDistance_le
      hw0 hw1 half stage (X.seq anchor) (Y.seq anchor)
      tiny htiny hanchorInput hcentralRate
    have hright := sameCutoffAnchorDistance_le
      hw0 hw1 half stage (Y.seq rightIndex) (Y.seq anchor)
      tiny htiny hrightInput hYpaid.2.2
    let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
    let leftPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq leftIndex)
    let leftAnchor := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (X.seq anchor)
    let rightAnchor := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (Y.seq anchor)
    let rightPoint := centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half (Y.seq rightIndex)
    have hrightSymm : CReal.leEv (D.distSq rightAnchor rightPoint)
        (CReal.ofQ' tiny) :=
      CReal.leEv_trans
        (CReal.leEv_of_equiv (D.distSq_symm rightAnchor rightPoint))
        hright
    exact distSq_threeLeg_le_of_sixteenth (D := D)
      leftPoint leftAnchor rightAnchor rightPoint epsilon hepsilon
      hleft hmiddle hrightSymm

theorem centralPhysicalAdaptiveMarkovMap_completionRel
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    {X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).CompletionRel X Y) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).CompletionRel
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise X)
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise Y) := by
  rcases h with ⟨hdata⟩
  exact ⟨centralPhysicalAdaptiveMarkovMapClose pointwise hdata⟩

/-! ## 3. Quotient descent and dense agreement -/

/-- The actual adaptive completed transfer, requiring only one pointwise
cross-cutoff Cauchy modulus for each dense finite-linear observable. -/
def centralPhysicalAdaptiveCompletedMarkovTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  Quotient.lift
    (fun X => Quotient.mk
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).completionSetoid
      (centralPhysicalAdaptiveMarkovMapCauchy pointwise X))
    (fun _ _ h => Quotient.sound
      (centralPhysicalAdaptiveMarkovMap_completionRel pointwise h))

@[simp] theorem centralPhysicalAdaptiveCompletedMarkovTransfer_mk
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).completionSetoid X) =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalAdaptiveMarkovMapCauchy pointwise X) := rfl

private def cauchyCloseOfSeqEq
    {D : SquaredSeminorm} (X Y : D.Cauchy)
    (hseq : forall n, X.seq n = Y.seq n) : D.Close X Y where
  modulus := fun _ => 0
  close := by
    intro epsilon hepsilon n _
    rw [hseq n]
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv (D.distSq_refl (Y.seq n)))
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon)))

/-- On dense embedded observables, the adaptive completed transfer is exactly
the previously constructed pointwise cutoff limit. -/
theorem centralPhysicalAdaptiveCompletedMarkovTransfer_embed
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (observable : CentralPhysicalLinearObservable) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (embedCentralPhysicalLinearObservable hw0 hw1 half observable) =
      centralPhysicalLinearMarkovDenseTransfer pointwise observable := by
  apply Quotient.sound
  exact ⟨cauchyCloseOfSeqEq
    (centralPhysicalAdaptiveMarkovMapCauchy pointwise
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant observable))
    (centralPhysicalLinearMarkovCutoffCauchy
      (pointwise.modulus observable))
    (fun _ => rfl)⟩

/-- The adaptive completed transfer fixes the normalized completed vacuum. -/
theorem centralPhysicalAdaptiveCompletedMarkovTransfer_vacuum
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half) :
    centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half := by
  exact Eq.trans
    (centralPhysicalAdaptiveCompletedMarkovTransfer_embed
      pointwise centralPhysicalLinearVacuum)
    (centralPhysicalLinearMarkovDenseTransfer_vacuum pointwise)

#print axioms centralPhysicalAdaptiveMarkovMapClose
#print axioms centralPhysicalAdaptiveMarkovMap_completionRel
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_embed
#print axioms centralPhysicalAdaptiveCompletedMarkovTransfer_vacuum

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
