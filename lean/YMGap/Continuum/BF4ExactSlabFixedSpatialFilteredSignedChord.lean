/-
# Retain the original word cross terms in the filtered OWN ceiling

The matched chord is bounded by its linear per-link cost PLUS the exact
signed cross moment of the ordered telescope. The original cap-four
common-tail comparison carries this sum to the mixed window (n,1,n+1).
All original weights, the OWN odd mean/variance, the even partition and
the radial, Young and drift corrections remain. No cross sign, useful
relative budget or justified physical scaling family is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSignedChord
import YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthChordalInsertion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredSignedChord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
  (edgeMoment mean_square_le_four)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
  (mixedDensity_window_pairing terminalEdge_probe_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling (mixedWordQuarticRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion (mixedQuarticDepthCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthChordalInsertion (wordChordal_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSignedChord
  (normalizedWordCross matched_word_signed_chord_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff (quarticCutoff)
open YMGap.Continuum.PositiveContractionResidual (geometric_bound)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage oddMass weightedMass mixRate windowRatio

private theorem matched_window_pin {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (loop : SourceLoop width) :
    windowRatio hw0 hw1 K width hK n 1 n (wordChordal width loop) ≈
      edgeMoment hw0 hw1 K width hK n (wordChordal width loop) := by
  have hp := terminalEdge_probe_pairing w K width n n (wordChordal_interval width loop).support
  unfold windowRatio massRatio edgeMoment oddMass
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hp)

private theorem clear_bound (M Z b : Q') (hz : (0 : Q')<Z)
    (h : M*Q'.recipPos Z hz≤b) : M≤b*Z := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hz)
  have hc : (M*Q'.recipPos Z hz)*Z ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hz)))
        (Q'.mul_one_eqv M))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc) hb

/-- Linear positive cost plus the literal signed matched cross moment.
This is NOT a linear total-cost bound: the cross moment is unestimated. -/
theorem mixedChordMoment_signed_bound {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K)
    (hkin : sufficientCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width) :
    mixedChordMoment w K width n loop≤
      ((6*(1-w)*Q'.ofNat loop.edges.length+
        2*normalizedWordCross hw0 hw1 K width hK n loop)+
        mixRate hw0 hw1 width^n*8)*evenPartition w K width n := by
  let I := wordChordal_interval width loop
  have hb := (windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)).1
  have hm := matched_word_signed_chord_bound hw0 hw1 K width hK hK1 hkin n loop hactive
  let b := 6*(1-w)*Q'.ofNat loop.edges.length+
    2*normalizedWordCross hw0 hw1 K width hK n loop
  have hs : windowRatio hw0 hw1 K width hK n 1 (n+1) (wordChordal width loop)≤
      b+mixRate hw0 hw1 width^n*8 :=
    Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (matched_window_pin hw0 hw1 K width hK n loop)) hm))
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : (4 : Q')+4 ≈ 8)))))
  let Z := weightedMass w K width (polyMul (terminalMessage w K width (n+1))
    (terminalMessage w K width (n+1)))
  let M := weightedMass w K width (polyMul (observedMessage w K width n 1 (wordChordal width loop))
    (terminalMessage w K width (n+1)))
  let hz := terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)
  have hh : M*Q'.recipPos Z hz≤b+mixRate hw0 hw1 width^n*8 := by
    simpa only [windowRatio, massRatio] using hs
  have hZ : Z ≈ evenPartition w K width n := by
    have h := evenPartition_middle_pin w K width n
    rw [terminalMessage_next w K width n] at h
    exact Q'.eqv_symm h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixedDensity_window_pairing w K width n I.support))
    (Q'.le_trans' _ _ _ (clear_bound M Z _ hz hh)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hZ)))

/-- Pay only the boundary-forgetting error at its SAME computed onset. -/
theorem mixedChordMoment_signed_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q')) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K)
    (hkin : sufficientCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    mixedChordMoment w K width n loop≤
      (6*(1-w)*Q'.ofNat loop.edges.length+
        2*normalizedWordCross hw0 hw1 K width hK n loop+epsilon)*
        evenPartition w K width n := by
  have hs := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (by decide : (0 : Q')≤32) he n hn
  have hsmall : mixRate hw0 hw1 width^n*8≤epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (by decide : (8 : Q')≤32) (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) n)) hs
  exact Q'.le_trans' _ _ _ (mixedChordMoment_signed_bound hw0 hw1 K width hK hK1 hkin n loop hactive)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_add_left _ _ _ hsmall)
      (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n)))

/-- The COMPLETE filtered OWN ceiling retains the ordered signed cross cost,
in addition to all three original radial, Young and drift corrections. -/
theorem filtered_loop_own_young_signed_chord {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K) (hkin : sufficientCutoff w≤K)
    (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) (t : Q') (ht : (0 : Q')≤t) :
    let c := ownMean hw0 hw1 K width hK n loop
    ((t*numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1)))+
      2*(t*mixedRadialCenteredMoment hw0 hw1 K width hK n loop))+
      2*mixedYoungSquareMoment hw0 hw1 K width hK n loop t)+
      2*(t*driftSquare w K width n (sourceCharacter width loop.edges 1))≤
    2*(evenPartition w K width n*
      ((t*t)*(oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+epsilon)+
        (t+c*c)*mixedWordQuarticRate w epsilon loop+
        (t*(4-c*c))*(6*(1-w)*Q'.ofNat loop.edges.length+
          2*normalizedWordCross hw0 hw1 K width hK n loop+epsilon))) := by
  let c := ownMean hw0 hw1 K width hK n loop
  let Z := evenPartition w K width n
  let v := oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)
  let b := mixedWordQuarticRate w epsilon loop
  let l := 6*(1-w)*Q'.ofNat loop.edges.length+
    2*normalizedWordCross hw0 hw1 K width hK n loop+epsilon
  have hgap : (0 : Q')≤t*(4-c*c) :=
    Q'.mul_nonneg _ _ ht (Q'.sub_nonneg_of_le (mean_square_le_four hw0 hw1 K width hK n loop))
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (t*(4-c*c))
    (mixedChordMoment_signed_tolerance_bound hw0 hw1 he K width hK hK1 hkin n loop hactive hn) hgap
  have hb := Q'.mul_le_mul_of_nonneg_left _ _ 2
    (Q'.add_le_add_left (Z*((t*t)*(v+epsilon)+(t+c*c)*b)) _ _ hl) (by decide)
  have hc : 2*(Z*((t*t)*(v+epsilon)+(t+c*c)*b)+(t*(4-c*c))*(l*Z)) ≈
      2*(Z*((t*t)*(v+epsilon)+(t+c*c)*b+(t*(4-c*c))*l)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.mul (.var 3) (.var 0)))))
      (.mul (.const 2) (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3)))))
      (by decide) (fun
        | 0 => Z
        | 1 => (t*t)*(v+epsilon)+(t+c*c)*b
        | 2 => t*(4-c*c)
        | _ => l)
  exact Q'.le_trans' _ _ _ (filtered_loop_own_young_paid hw0 hw1 hw he K width hK n loop
    hactive hcut hn t ht) (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hc))

#print axioms mixedChordMoment_signed_bound
#print axioms mixedChordMoment_signed_tolerance_bound
#print axioms filtered_loop_own_young_signed_chord

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredSignedChord
