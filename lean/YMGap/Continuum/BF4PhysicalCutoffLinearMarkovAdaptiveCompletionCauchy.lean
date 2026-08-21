/-
# The adaptive BF4 Markov completion diagonal is Cauchy

The preceding schedule makes every late action cutoff pay two classes of
finite-prefix obligations.  This file contracts those local witnesses into
the first global completion theorem: for every input Cauchy representative
`X`, the two-index sequence

  `K |-> P_K (X_{i_X(K)})`

is a genuine Cauchy representative.

For two late action cutoffs, use one fixed earlier input anchor.  Each selected
input term is close to that anchor by input Cauchyness; regularized same-cutoff
nonexpansiveness controls the two outer action legs; and the pointwise
cross-cutoff modulus controls the middle action leg.  Two sqrt-free triangle
estimates cost ten copies of a sixteenth tolerance, still below the requested
tolerance.

## Axiom gate

Only explicit schedule rates, finite triangle estimates, rational tolerance
splitting, and the supplied pointwise Cauchy family are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Rational error budget -/

def adaptiveQuarter (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

def adaptiveSixteenth (epsilon : Q') : Q' :=
  adaptiveQuarter (adaptiveQuarter epsilon)

theorem adaptiveQuarter_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < adaptiveQuarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)

theorem adaptiveSixteenth_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < adaptiveSixteenth epsilon :=
  adaptiveQuarter_pos (adaptiveQuarter_pos hepsilon)

/-- The nested two-triangle budget is ten sixteenths of `epsilon`. -/
theorem ten_sixteenths_le (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    let tiny := adaptiveSixteenth epsilon
    let twice := tiny + tiny
    let four := twice + twice
    twice + (four + four) <= epsilon := by
  let tiny := adaptiveSixteenth epsilon
  let twice := tiny + tiny
  let four := twice + twice
  have htiny : (0 : Q') <= tiny :=
    Q'.le_of_lt (adaptiveSixteenth_pos hepsilon)
  have htwice : (0 : Q') <= twice :=
    Q'.zero_le_add tiny tiny htiny htiny
  have hfour : (0 : Q') <= four :=
    Q'.zero_le_add twice twice htwice htwice
  have hfirst : twice + (four + four) <= four + (four + four) :=
    Q'.add_le_add
      (Q'.add_le_self_of_nonneg twice twice htwice)
      (Q'.le_refl' (four + four))
  have hsecond : four + (four + four) <=
      (four + four) + (four + four) :=
    Q'.add_le_add
      (Q'.add_le_self_of_nonneg four four hfour)
      (Q'.le_refl' (four + four))
  have htwiceEq : twice.eqv
      (HalfPow.half * adaptiveQuarter epsilon) :=
    ExpNeg.two_halves (HalfPow.half * adaptiveQuarter epsilon)
  have hfourEq : four.eqv (adaptiveQuarter epsilon) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right twice
        (HalfPow.half * adaptiveQuarter epsilon) twice htwiceEq)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (HalfPow.half * adaptiveQuarter epsilon)
          twice (HalfPow.half * adaptiveQuarter epsilon) htwiceEq)
        (ExpNeg.two_halves (adaptiveQuarter epsilon)))
  have heighthEq : (four + four).eqv (HalfPow.half * epsilon) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right four
        (adaptiveQuarter epsilon) four hfourEq)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (adaptiveQuarter epsilon)
          four (adaptiveQuarter epsilon) hfourEq)
        (ExpNeg.two_halves (HalfPow.half * epsilon)))
  have hsixteenEq : ((four + four) + (four + four)).eqv epsilon := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (four + four)
        (HalfPow.half * epsilon) (four + four) heighthEq)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (HalfPow.half * epsilon)
          (four + four) (HalfPow.half * epsilon) heighthEq)
        (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hsixteenEq))

/-! ## 2. One same-cutoff anchor leg -/

theorem sameCutoffAnchorDistance_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (selected anchor : CentralPhysicalLinearObservable)
    (tolerance : Q') (htolerance : (0 : Q') < tolerance)
    (hinput : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half selected anchor)
      (CReal.ofQ' (HalfPow.half * tolerance)))
    (hrate :
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          selected anchor)).rate
            (HalfPow.half * (HalfPow.half * tolerance)) <= cutoff) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half selected)
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half anchor))
      (CReal.ofQ' tolerance) := by
  let slack := HalfPow.half * tolerance
  have hslack : (0 : Q') < slack :=
    ExpNeg.half_mul_pos tolerance htolerance
  have hmarkov :=
    physicalLinearDistSq_markovCutoffAction_le_add_regularized
      hw0 hw1 half cutoff selected anchor slack hslack hrate
  have hsum : CReal.leEv
      (CReal.add
        (physicalLinearDistSq hw0 hw1 half selected anchor)
        (CReal.ofQ' slack))
      (CReal.add (CReal.ofQ' slack) (CReal.ofQ' slack)) :=
    CReal.leEv_add hinput (CReal.leEv_refl (CReal.ofQ' slack))
  have hconstant : CReal.leEv
      (CReal.add (CReal.ofQ' slack) (CReal.ofQ' slack))
      (CReal.ofQ' tolerance) := by
    rw [CReal.ofQ'_add]
    exact CReal.leEv_of_le
      (CReal.ofQ'_le_ofQ'
        (Q'.le_of_eqv (ExpNeg.two_halves tolerance)))
  exact CReal.leEv_trans hmarkov
    (CReal.leEv_trans hsum hconstant)

/-- Three consecutive squared-distance legs, each bounded by one sixteenth of
the target tolerance, fit through two sqrt-free triangle estimates. -/
theorem distSq_threeLeg_le_of_sixteenth
    {D : SquaredSeminorm}
    (left firstAnchor secondAnchor right : D.Carrier)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hleft : CReal.leEv (D.distSq left firstAnchor)
      (CReal.ofQ' (adaptiveSixteenth epsilon)))
    (hmiddle : CReal.leEv (D.distSq firstAnchor secondAnchor)
      (CReal.ofQ' (adaptiveSixteenth epsilon)))
    (hright : CReal.leEv (D.distSq secondAnchor right)
      (CReal.ofQ' (adaptiveSixteenth epsilon))) :
    CReal.leEv (D.distSq left right) (CReal.ofQ' epsilon) := by
  let tiny := adaptiveSixteenth epsilon
  have hinner : CReal.leEv (D.distSq firstAnchor right)
      (CReal.add
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))) :=
    CReal.leEv_trans
      (D.distSq_triangle firstAnchor secondAnchor right)
      (CReal.leEv_add
        (CReal.leEv_add hmiddle hmiddle)
        (CReal.leEv_add hright hright))
  have htotal : CReal.leEv (D.distSq left right)
      (CReal.add
        (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
        (CReal.add
          (CReal.add
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)))
          (CReal.add
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
            (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))))) :=
    CReal.leEv_trans
      (D.distSq_triangle left firstAnchor right)
      (CReal.leEv_add
        (CReal.leEv_add hleft hleft)
        (CReal.leEv_add hinner hinner))
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

/-! ## 3. The actual adaptive output representative -/

def adaptiveMarkovCauchyThreshold
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  let slack := HalfPow.half * tiny
  let pairTolerance := HalfPow.half * slack
  max (X.modulus slack)
    (max (CReal.lv tiny) (CReal.lv pairTolerance))

def centralPhysicalAdaptiveMarkovMapCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage :=
    centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half
      (X.seq (centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X stage))
  modulus epsilon := centralPhysicalAdaptiveMarkovSampleRate
    hw0 hw1 half pointwise X (adaptiveMarkovCauchyThreshold X epsilon)
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    let tiny := adaptiveSixteenth epsilon
    let slack := HalfPow.half * tiny
    let pairTolerance := HalfPow.half * slack
    let anchor := X.modulus slack
    let firstIndex := centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X first
    let secondIndex := centralPhysicalAdaptiveMarkovSampleIndex
      hw0 hw1 half pointwise X second
    have htiny : (0 : Q') < tiny := adaptiveSixteenth_pos hepsilon
    have hslack : (0 : Q') < slack :=
      ExpNeg.half_mul_pos tiny htiny
    have hpairTolerance : (0 : Q') < pairTolerance :=
      ExpNeg.half_mul_pos slack hslack
    have hfirstPaid := centralPhysicalAdaptiveMarkov_requirements_paid
      hw0 hw1 half pointwise X anchor tiny pairTolerance
      htiny hpairTolerance first hfirst
    have hsecondPaid := centralPhysicalAdaptiveMarkov_requirements_paid
      hw0 hw1 half pointwise X anchor tiny pairTolerance
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
    have hinner : CReal.leEv (D.distSq firstAnchor rightPoint)
        (CReal.add
          (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
          (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))) :=
      CReal.leEv_trans
        (D.distSq_triangle firstAnchor secondAnchor rightPoint)
        (CReal.leEv_add
          (CReal.leEv_add hmiddle hmiddle)
          (CReal.leEv_add hrightSymm hrightSymm))
    have htotal : CReal.leEv (D.distSq leftPoint rightPoint)
        (CReal.add
          (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
          (CReal.add
            (CReal.add
              (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
              (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny)))
            (CReal.add
              (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))
              (CReal.add (CReal.ofQ' tiny) (CReal.ofQ' tiny))))) :=
      CReal.leEv_trans
        (D.distSq_triangle leftPoint firstAnchor rightPoint)
        (CReal.leEv_add
          (CReal.leEv_add hleft hleft)
          (CReal.leEv_add hinner hinner))
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

#print axioms centralPhysicalAdaptiveMarkovMapCauchy
#print axioms distSq_threeLeg_le_of_sixteenth

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
