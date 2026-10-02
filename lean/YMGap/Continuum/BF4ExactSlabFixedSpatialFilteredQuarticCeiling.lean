/-
# Pay the quartic term of the ORIGINAL signed filtered source

The actual mixed-depth selected-link producer and the ordered quaternion
word telescope pay the COMPLETE word quartic correction against the SAME
even partition. The original radial-minus-drift term is left signed.
Both regulator onsets are computed. The coefficient retains 16*length^4;
it is not a uniform loop-size, OWN-variance or physical scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (lower_supported upper_supported lower_unit upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (numerator driftSquare evenPartition evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin (quarticProfileCoefficient)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff (quarticCutoff)
open YMGap.Continuum.QuaternionHaarWordQuartic (wordFourthFactor word_norm_quartic_bound)
open YMGap.Continuum.BF4DyadicWilsonSquare (side square paddedSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (includedLoop_edges_active)

/-- Explicit nome, tolerance and literal path-length dependence. -/
def mixedWordQuarticRate (w epsilon : Q') {width : Nat} (loop : SourceLoop width) : Q' :=
  wordFourthFactor loop.edges.length * (quarticProfileCoefficient w+2*epsilon)

/-- An actual complete-word estimate, not a supplied source-norm comparison.
Repeated links and shared variables stay inside the same certified measure. -/
theorem mixed_word_quartic_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    mixedQuarticMoment w K width n loop ≤
      mixedWordQuarticRate w epsilon loop * evenPartition w K width n := by
  have h := word_norm_quartic_bound
    (mixedDensity_certificate hw0 hw1 K width hK n)
    (orientedLink width) (upperOriented width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
    (fun e he => upper_supported (loop.physical e he))
    (fun e he => lower_unit (loop.physical e he))
    (fun e he => upper_unit (loop.physical e he)) _
    (fun e hmem => oriented_link_fourth_tolerance_bound hw0 hw1 hw he K width hK n e
      (loop.physical e hmem) (hactive e hmem) hcut hn)
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))

/-- The literal signed radius-two source has its quartic correction paid.
The full original radial term and minus TWICE its drift remain together. -/
theorem filtered_loop_quartic_paid {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≤
      (2*mixedRadialMoment w K width n loop+
        2*(mixedWordQuarticRate w epsilon loop*evenPartition w K width n))+
      -(2*driftSquare w K width n (sourceCharacter width loop.edges 1)) :=
  Q'.le_trans' _ _ _ (filtered_loop_radial_drift_bound hw0 hw1 K width hK n loop)
    (Q'.add_le_add
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2
        (mixed_word_quartic_tolerance_bound hw0 hw1 hw he K width hK n loop hactive hcut hn)
        (by decide))) (Q'.le_refl' _))

/-- The normalized SAME original window, without changing its even Z. -/
theorem filtered_loop_quartic_paid_normalized {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    windowRatio hw0 hw1 K width hK n 2 n
      (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≤
      ((2*mixedRadialMoment w K width n loop+
        2*(mixedWordQuarticRate w epsilon loop*evenPartition w K width n))+
      -(2*driftSquare w K width n (sourceCharacter width loop.edges 1)))*
        Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n) := by
  have hq := mixed_word_quartic_tolerance_bound hw0 hw1 hw he K width hK n loop hactive hcut hn
  have hu := Q'.add_le_add
    (Q'.add_le_add_left (2*mixedRadialMoment w K width n loop) _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hq (by decide)))
    (Q'.le_refl' (-(2*driftSquare w K width n (sourceCharacter width loop.edges 1))))
  exact Q'.le_trans' _ _ _ (filtered_loop_radial_drift_normalized hw0 hw1 K width hK n loop)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hu
      (Q'.le_of_lt (Q'.recipPos_pos _ (evenPartition_positive hw0 hw1 K width hK n))))

/-- The actual padded dyadic square discharges active-link hypotheses.
No new observable, center, norm or changing-family input is supplied. -/
theorem paddedSquare_filtered_quartic_paid {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n scale : Nat) (hwidth : side scale<width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    let loop := paddedSquare scale width hwidth
    numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≤
      (2*mixedRadialMoment w K width n loop+
        2*(mixedWordQuarticRate w epsilon loop*evenPartition w K width n))+
      -(2*driftSquare w K width n (sourceCharacter width loop.edges 1)) :=
  filtered_loop_quartic_paid hw0 hw1 hw he K width hK n (paddedSquare scale width hwidth)
    (includedLoop_edges_active hwidth (square scale)) hcut hn

#print axioms mixedWordQuarticRate
#print axioms mixed_word_quartic_tolerance_bound
#print axioms filtered_loop_quartic_paid
#print axioms filtered_loop_quartic_paid_normalized
#print axioms paddedSquare_filtered_quartic_paid

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling
