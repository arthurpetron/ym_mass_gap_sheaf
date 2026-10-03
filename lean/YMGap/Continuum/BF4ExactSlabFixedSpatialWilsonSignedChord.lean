/-
# Original matched Wilson chord with its actual signed cross retained

The ordered word costs length times the single-link diagonal budget,
PLUS twice the computed signed cross insertion. All spatial/terminal
factors remain in the ORIGINAL matched edge density. Normalization uses
the SAME oddMass; no sign of the cross or variance comparison is assumed.
The actual kinetic cutoff is K, with K>=1 and sufficientCutoff<=K explicit.
This supplies a finite source-aware cost, not a changing-family budget.
-/

import YMGap.Continuum.QuaternionHaarWordSignedCross
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSignedChord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic (lower_unit upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper (oriented_displacement_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (edgeMoment)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarWordSignedCross

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass edgeMoment wordChordal

/-- Literal ordered signed cross under the full original matched edge law. -/
def wordCross (w : Q') (K width depth : Nat) (loop : SourceLoop width) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth))
      (wordCrossPolynomial (orientedLink width) (upperOriented width) loop.edges))

def wordDiagonal (w : Q') (K width depth : Nat) (loop : SourceLoop width) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth))
      (wordDiagonalPolynomial (orientedLink width) (upperOriented width) loop.edges))

/-- No new density or center: only the SAME original odd partition divides
the computed signed insertion. -/
def normalizedWordCross {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width) : Q' :=
  wordCross w K width depth loop *
    Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)

/-- The exact full-word norm is the diagonal plus TWICE its actual signed
pair sum, with every original source factor retained. -/
theorem matched_word_signed_chord_identity (w : Q') (K width depth : Nat)
    (loop : SourceLoop width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (wordChordal width loop)) ≈
      wordDiagonal w K width depth loop + 2*wordCross w K width depth loop := by
  simpa only [wordChordal, wordDiagonal, wordCross] using
    (word_weighted_cross_identity (N width+N width)
      (edgeDensity w K width (terminalMessage w K width depth))
      (orientedLink width) (upperOriented width) loop.edges)

/-- Linear diagonal length, not length squared; no cross sign hypothesis. -/
theorem matched_word_signed_chord_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK1 : 1 ≤ K) (hkin : sufficientCutoff w ≤ K) (depth : Nat)
    (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (wordChordal width loop)) ≤
      (6*(1-w)*Q'.ofNat loop.edges.length)*oddMass w K width depth +
        2*wordCross w K width depth loop := by
  have hpred : K-1+1 = K := Nat.sub_add_cancel hK1
  have hkin' : sufficientCutoff w ≤ K-1+1 := by rwa [hpred]
  have hd := word_diagonal_bound
    (edgeDensity w K width (terminalMessage w K width depth))
    ((6*(1-w))*oddMass w K width depth)
    (orientedLink width) (upperOriented width) loop.edges
    (fun e he => lower_unit (loop.physical e he))
    (fun e he => upper_unit (loop.physical e he))
    (fun e he => by
      have h := oriented_displacement_bound hw0 hw1 (K-1) width depth hkin'
        (loop.physical e he) (hactive e he)
      simpa only [hpred] using h)
  have hr : Q'.ofNat loop.edges.length*((6*(1-w))*oddMass w K width depth) ≈
      (6*(1-w)*Q'.ofNat loop.edges.length)*oddMass w K width depth :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide) (fun
        | 0 => Q'.ofNat loop.edges.length | 1 => 6*(1-w)
        | _ => oddMass w K width depth)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (matched_word_signed_chord_identity w K width depth loop))
    (Q'.add_le_add_right _ _ _ (Q'.le_trans' _ _ _ hd (Q'.le_of_eqv hr)))

private theorem normalize_signed (A rate X Z : Q') (hZ : (0 : Q') < Z)
    (h : A ≤ rate*Z+2*X) :
    A*Q'.recipPos Z hZ ≤ rate+2*(X*Q'.recipPos Z hZ) := by
  let r := Q'.recipPos Z hZ
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ h
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  have hr : (rate*Z+2*X)*r ≈ rate*(Z*r)+2*(X*r) :=
    poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2))) (.var 3))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 3)))
        (.mul (.const 2) (.mul (.var 2) (.var 3)))) (by decide) (fun
          | 0 => rate | 1 => Z | 2 => X | _ => r)
  have hc : rate*(Z*r)+2*(X*r) ≈ rate+2*(X*r) :=
    Q'.add_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left rate _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv rate))
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hr hc))

/-- The finite SAME-source cost requested by the mixed-depth consumer.
K is the ACTUAL cutoff; positivity, K>=1 and kinetic onset stay separate. -/
theorem matched_word_signed_chord_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (hkin : sufficientCutoff w ≤ K)
    (depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    edgeMoment hw0 hw1 K width hK depth (wordChordal width loop) ≤
      6*(1-w)*Q'.ofNat loop.edges.length +
        2*normalizedWordCross hw0 hw1 K width hK depth loop := by
  unfold edgeMoment normalizedWordCross
  exact normalize_signed _ _ _ _ (oddMass_positive hw0 hw1 K width hK depth)
    (matched_word_signed_chord_cleared hw0 hw1 K width hK1 hkin depth loop hactive)

#print axioms wordCross
#print axioms wordDiagonal
#print axioms normalizedWordCross
#print axioms matched_word_signed_chord_identity
#print axioms matched_word_signed_chord_cleared
#print axioms matched_word_signed_chord_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSignedChord
